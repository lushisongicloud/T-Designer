#ifndef DEEPSEEKCLIENT_H
#define DEEPSEEKCLIENT_H

#include <QObject>
#include <QString>
#include <QJsonObject>
#include <QJsonArray>
#include <QNetworkAccessManager>
#include <QNetworkReply>

class DeepSeekClient : public QObject
{
    Q_OBJECT

public:
    explicit DeepSeekClient(QObject *parent = nullptr);
    ~DeepSeekClient();

    // 设置 API Key
    void setApiKey(const QString &apiKey);
    
    // 发送聊天请求（支持流式输出）
    void chatCompletion(const QString &systemPrompt, const QString &userMessage, bool stream = true);
    
    // 取消当前请求
    void cancelRequest();

signals:
    // 流式输出时的增量内容（reasoning 或 content）
    void reasoningDelta(const QString &delta);
    void contentDelta(const QString &delta);
    
    // 完整响应（非流式或流式结束时）
    void responseComplete(const QString &reasoning, const QString &content);
    
    // 错误信号
    void errorOccurred(const QString &error);

private slots:
    void onNetworkReplyFinished();
    void onNetworkReplyReadyRead();

private:
    QString m_apiKey;
    QNetworkAccessManager *m_networkManager;
    QNetworkReply *m_currentReply;
    
    QString m_accumulatedReasoning;
    QString m_accumulatedContent;
    QByteArray m_buffer;  // 用于处理分块的 SSE 数据
    
    void processStreamLine(const QString &line);
    QJsonObject buildRequestBody(const QString &systemPrompt, const QString &userMessage, bool stream);
};

#endif // DEEPSEEKCLIENT_H
