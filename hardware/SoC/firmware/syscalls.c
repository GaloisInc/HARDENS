#include <errno.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <sys/time.h>

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

#define UART_TX_REG 0x02000000
#define MIN_PRINT_DELAY_TICKS 1000
int _write(int file, char *ptr, int len)
{
    volatile uint32_t *uart_tx = (void*) UART_TX_REG;
    (void)file;
    for (int i=0;i<len;i++) {
    	*uart_tx = ptr[i];
        uint32_t count = MIN_PRINT_DELAY_TICKS;
        while(count-->0) {
            __asm__ volatile ("nop");
        }
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
