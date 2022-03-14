TARGET=riscv64-unknown-elf

ARCH 		= -march=rv32i
ABI 		= -mabi=ilp32

CC		= $(TARGET)-gcc
OBJDUMP	= $(TARGET)-objdump
OBJCOPY	= $(TARGET)-objcopy
LDLIBS	 =  -lc -lgcc
WERROR ?= -Werror

COMPILER_FLAGS = -mcmodel=medany

# Use main_blinky as demo source and target file name if not specified
PROG 	?= firmware
CRT0	= boot.S
# Optimize for size
OPT = -Os

WARNINGS = -Wextra -Wshadow -Wpointer-arith -Wcast-align -Wsign-compare \
		-Waggregate-return -Wmissing-declarations -Wunused $(WERROR) 
C_WARNINGS = -Wbad-function-cast -Wmissing-prototypes -Wstrict-prototypes

INCLUDES = -I. -I../../../src/include

DEMO_SRC = firmware.c
APP_SRC = syscalls.c \
	bsp.c printf.c

ASFLAGS  += -g $(ARCH) $(ABI) -Wa,-Ilegacy
CFLAGS += $(OPT) -g3 $(ARCH) $(ABI) $(COMPILER_FLAGS) $(WARNINGS) $(C_WARNINGS) $(INCLUDES) -DPRINTF_INCLUDE_CONFIG_H
LDFLAGS	 += -Wl,-Bstatic,-T,sections.ld,--strip-debug -nostartfiles -nostdlib $(ARCH) $(ABI)
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
	@$(OBJDUMP) -S -D $(PROG).elf > $(PROG).asm	
	@echo Completed $@
	@cp $(PROG).elf text.elf
	@$(OBJCOPY) -j .text text.elf
	@$(OBJDUMP) -S -D text.elf > text.asm
#	@cp $(PROG).elf dmem.elf
#	@$(OBJCOPY) -R text dmem.elf
#	@$(OBJCOPY) -R .text dmem.elf
#	@$(OBJDUMP) -S -D dmem.elf > dmem.asm
#	@mv dmem.elf $(PROG).elf
#	@$(OBJDUMP) -S -D $(PROG).elf > $(PROG).asm

clean :
	@rm -f $(OBJS)
	@rm -f *.elf
	@rm -f *.asm
	@find ../../../ -iname '*.o' -exec rm -rf {} \;

