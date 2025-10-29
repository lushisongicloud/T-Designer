#include "componententity.h"

ComponentEntity::ComponentEntity()
{

}
void ComponentEntity::deletePort(const QString& port_temp)
{
    for(int i=0; i<port.length();i++)
        if(port[i] == port_temp)
        {
            port.removeAt(i);
            return;
        }
}
int ComponentEntity::findPort(const QString& port_temp) const
{
    for(int i=0; i<port.length();i++)
        if(port[i] == port_temp)
            return i;

    return -1;
}
