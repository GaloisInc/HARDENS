#ifndef SYSCALLS_H_
#define SYSCALLS_H_


void *_sbrk(int nbytes);
int _write(int file, char *ptr, int len);
int _close(int fd);
int _fstat(int fd, void *buffer);
long _lseek(int fd, long offset, int origin);
int _read(int fd, void *buffer, unsigned int count);
int _isatty(int fd);
int _kill(int pid, int sig);
int _getpid(int n);
void _exit(int n);

#endif // SYSCALLS_H_