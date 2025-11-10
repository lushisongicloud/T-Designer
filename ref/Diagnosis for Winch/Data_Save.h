#ifndef DATA_SAVE_H
#define DATA_SAVE_H
void signal_handler();
void set_Recording_timer();
void IfClose();
extern void SaveThread();
extern int gettimeofday(struct timeval *tp, void *tzp);
#endif // DATA_SAVE_H
