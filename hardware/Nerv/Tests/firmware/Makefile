TARGET=riscv64-unknown-elf

ARCH 		= -march=rv32im
ABI 		= -mabi=ilp32

CC		= $(TARGET)-gcc
OBJDUMP	= $(TARGET)-objdump
LDLIBS	 =  -lc -lgcc
WERROR ?= -Werror

COMPILER_FLAGS = -mcmodel=medany

# Use main_blinky as demo source and target file name if not specified
PROG 	?= firmware
CRT0	= boot.S

WARNINGS = -Wextra -Wshadow -Wpointer-arith -Wcast-align -Wsign-compare \
		-Waggregate-return -Wmissing-declarations -Wunused $(WERROR) 
C_WARNINGS = -Wbad-function-cast -Wmissing-prototypes -Wstrict-prototypes

INCLUDES = -I.

DEMO_SRC = firmware.c
APP_SRC = syscalls.c

ASFLAGS  += -g $(ARCH) $(ABI) -Wa,-Ilegacy
CFLAGS += $(OPT) -g3 $(ARCH) $(ABI) $(COMPILER_FLAGS) $(WARNINGS) $(C_WARNINGS) $(INCLUDES)
LDFLAGS	 += -T sections.lds -nostartfiles -nostdlib $(ARCH) $(ABI)
#
# Define all object files.
#
APP_OBJ  = $(APP_SRC:.c=.o)
DEMO_OBJ = $(DEMO_SRC:.c=.o)
CRT0_OBJ = $(CRT0:.S=.o)
OBJS = $(CRT0_OBJ) $(DEMO_OBJ) $(APP_OBJ)

$(info ASFLAGS=$(ASFLAGS))
$(info LDLIBS=$(LDLIBS))
$(info CFLAGS=$(CFLAGS))
$(info LDFLAGS=$(LDFLAGS))

%.o: %.c
	@echo "    CC $<"
	@$(CC) -c $(CFLAGS) -o $@ $<

%.o: %.S
	@echo "    CC $<"
	@$(CC) $(ASFLAGS) -c $(CFLAGS) -o $@ $<

all: $(PROG).elf

$(PROG).elf  : $(OBJS) Makefile 
	@echo Linking....
	@$(CC) -o $@ $(LDFLAGS) $(OBJS) $(LDLIBS)
	@$(OBJDUMP) -S $(PROG).elf > $(PROG).asm	
	@echo Completed $@

clean :
	@rm -f $(OBJS)
	@rm -f $(PROG).elf 
	@rm -f $(PROG).asm
	@find ../../../ -iname '*.o' -exec rm -rf {} \;

