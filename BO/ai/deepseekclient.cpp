#include "deepseekclient.h"
#include <QJsonDocument>
#include <QNetworkRequest>
#include <QDebug>
#include <QEventLoop>
#include <QSslSocket>
#include <QSslConfiguration>
#include <QSslCipher>
#include <QSslError>

static void logSslEnvironmentOnce()
{
    static bool done = false;
    if (done) return;
    done = true;
    qDebug() << "[SSL] QSslSocket::supportsSsl=" << QSslSocket::supportsSsl();
    qDebug() << "[SSL] Build version=" << QSslSocket::sslLibraryBuildVersionString();
    qDebug() << "[SSL] Runtime version=" << QSslSocket::sslLibraryVersionString();
    const auto conf = QSslConfiguration::defaultConfiguration();
    qDebug() << "[SSL] Default protocol=" << conf.protocol();
    qDebug() << "[SSL] Cipher count=" << conf.ciphers().size();
    qDebug() << "[SSL] CA certificates count=" << conf.caCertificates().size();
    if (!QSslSocket::supportsSsl()) {
        qWarning() << "[SSL] 当前环境不支持 SSL。请确认应用目录下存在 libcrypto-1_1-x64.dll 与 libssl-1_1-x64.dll (Qt 5.12.x 需 OpenSSL 1.1.1)。";
    }
}

DeepSeekClient::DeepSeekClient(QObject *parent)
    : QObject(parent)
    , m_networkManager(new QNetworkAccessManager(this))
    , m_currentReply(nullptr)
{
    // 记录一次 SSL 环境信息，便于排查 TLS initialization failed
    logSslEnvironmentOnce();
}

DeepSeekClient::~DeepSeekClient()
{
    cancelRequest();
}

void DeepSeekClient::setApiKey(const QString &apiKey)
{
    m_apiKey = apiKey;
}

void DeepSeekClient::chatCompletion(const QString &systemPrompt, const QString &userMessage, bool stream)
{
    if (m_apiKey.isEmpty()) {
        emit errorOccurred("API Key 未设置");
        return;
    }

    if (!QSslSocket::supportsSsl()) {
        emit errorOccurred("当前环境不支持 SSL (缺少 OpenSSL DLL)");
        return;
    }
    
    // 取消之前的请求
    cancelRequest();
    
    // 重置累积内容
    m_accumulatedReasoning.clear();
    m_accumulatedContent.clear();
    m_buffer.clear();
    
    // 构建请求
    QNetworkRequest request(QUrl("https://api.deepseek.com/chat/completions"));
    request.setHeader(QNetworkRequest::ContentTypeHeader, "application/json");
    request.setRawHeader("Authorization", QString("Bearer %1").arg(m_apiKey).toUtf8());
    
    QJsonObject requestBody = buildRequestBody(systemPrompt, userMessage, stream);
    QByteArray requestData = QJsonDocument(requestBody).toJson(QJsonDocument::Compact);
    
    m_currentReply = m_networkManager->post(request, requestData);

    // 捕获底层 SSL 错误
    connect(m_currentReply, &QNetworkReply::sslErrors, this, [this](const QList<QSslError> &errors){
        QStringList msgs; for (const auto &e: errors) msgs << e.errorString();
        qWarning() << "DeepSeek SSL 错误:" << msgs.join(" | ");
    });
    
    if (stream) {
        connect(m_currentReply, &QNetworkReply::readyRead, this, &DeepSeekClient::onNetworkReplyReadyRead);
    }
    connect(m_currentReply, &QNetworkReply::finished, this, &DeepSeekClient::onNetworkReplyFinished);
}

void DeepSeekClient::cancelRequest()
{
    if (m_currentReply) {
        m_currentReply->abort();
        m_currentReply->deleteLater();
        m_currentReply = nullptr;
    }
}

void DeepSeekClient::onNetworkReplyFinished()
{
    if (!m_currentReply) {
        return;
    }
    
    if (m_currentReply->error() != QNetworkReply::NoError) {
        QString errorMsg = m_currentReply->errorString();
        if (m_currentReply->error() == QNetworkReply::SslHandshakeFailedError) {
            errorMsg += " | 提示: 请确认应用目录存在 OpenSSL 1.1.1 DLL (libcrypto-1_1-x64.dll, libssl-1_1-x64.dll) 且系统时间正确";
        }
        qWarning() << "DeepSeek API 错误:" << errorMsg;
        emit errorOccurred(errorMsg);
    } else {
        // 非流式输出，直接解析完整响应
        QByteArray responseData = m_currentReply->readAll();
        QJsonDocument doc = QJsonDocument::fromJson(responseData);
        
        if (doc.isObject()) {
            QJsonObject obj = doc.object();
            
            // 检查是否有错误
            if (obj.contains("error")) {
                QString error = obj["error"].toObject()["message"].toString();
                emit errorOccurred(error);
            } else if (obj.contains("choices")) {
                QJsonArray choices = obj["choices"].toArray();
                if (!choices.isEmpty()) {
                    QJsonObject message = choices[0].toObject()["message"].toObject();
                    
                    QString reasoning = message["reasoning_content"].toString();
                    QString content = message["content"].toString();
                    
                    emit responseComplete(reasoning, content);
                }
            }
        }
    }
    
    m_currentReply->deleteLater();
    m_currentReply = nullptr;
}

void DeepSeekClient::onNetworkReplyReadyRead()
{
    if (!m_currentReply) {
        return;
    }
    
    // 读取新数据并添加到缓冲区
    m_buffer.append(m_currentReply->readAll());
    
    // 按行处理 SSE 数据
    while (m_buffer.contains('\n')) {
        int pos = m_buffer.indexOf('\n');
        QByteArray line = m_buffer.left(pos);
        m_buffer.remove(0, pos + 1);
        
        QString lineStr = QString::fromUtf8(line).trimmed();
        if (!lineStr.isEmpty()) {
            processStreamLine(lineStr);
        }
    }
}

void DeepSeekClient::processStreamLine(const QString &line)
{
    // SSE 格式: "data: {json}"
    if (!line.startsWith("data: ")) {
        return;
    }
    
    QString jsonStr = line.mid(6).trimmed();
    
    // 检查是否是结束标记
    if (jsonStr == "[DONE]") {
        emit responseComplete(m_accumulatedReasoning, m_accumulatedContent);
        return;
    }
    
    // 解析 JSON
    QJsonDocument doc = QJsonDocument::fromJson(jsonStr.toUtf8());
    if (!doc.isObject()) {
        return;
    }
    
    QJsonObject obj = doc.object();
    QJsonArray choices = obj["choices"].toArray();
    
    if (choices.isEmpty()) {
        return;
    }
    
    QJsonObject delta = choices[0].toObject()["delta"].toObject();
    
    // 提取 reasoning_content
    if (delta.contains("reasoning_content")) {
        QString reasoning = delta["reasoning_content"].toString();
        m_accumulatedReasoning += reasoning;
        emit reasoningDelta(reasoning);
    }
    
    // 提取 content
    if (delta.contains("content")) {
        QString content = delta["content"].toString();
        m_accumulatedContent += content;
        emit contentDelta(content);
    }
}

QJsonObject DeepSeekClient::buildRequestBody(const QString &systemPrompt, const QString &userMessage, bool stream)
{
    QJsonObject body;
    body["model"] = "deepseek-reasoner";
    body["stream"] = stream;
    
    QJsonArray messages;
    
    // 系统提示
    if (!systemPrompt.isEmpty()) {
        QJsonObject systemMsg;
        systemMsg["role"] = "system";
        systemMsg["content"] = systemPrompt;
        messages.append(systemMsg);
    }
    
    // 用户消息
    QJsonObject userMsg;
    userMsg["role"] = "user";
    userMsg["content"] = userMessage;
    messages.append(userMsg);
    
    body["messages"] = messages;
    
    return body;
}
