#include <errno.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <sys/time.h>

volatile uint32_t *uart_tx = (void*)0x02000000;

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

void _exit(int n) {
    (void)n;
    while(1){
        ;;
    }
}

void *_sbrk(int nbytes)
{
    (void)nbytes;
    errno = ENOMEM;
    return (void *)-1;
}


int _write(int file, char *ptr, int len)
{
    (void)file;
    for (int i=0;i<len;i++) {
    	*uart_tx = ptr[len];
	}
    return len;
}

int _close(int fd)
{
    (void)fd;
    errno = EBADF;
    return -1;
}

long _lseek(int fd, long offset, int origin)
{
    (void)fd;
    (void)offset;
    (void)origin;
    errno = EBADF;
    return -1;
}

int _read(int fd, void *buffer, unsigned int count)
{
    (void)fd;
    (void)buffer;
    (void)count;
    errno = EBADF;
    return -1;
}

int _fstat(int fd, void *buffer)
{
    (void)fd;
    (void)buffer;
    errno = EBADF;
    return -1;
}

int _isatty(int fd)
{
    (void)fd;
    errno = EBADF;
    return 0;
}

int _kill(int pid, int sig)
{
    (void)pid;
    (void)sig;
    errno = EBADF;
    return -1;
}

int _getpid(int n)
{
    (void)n;
    return 1;
}
