TARGET=riscv64-unknown-elf

ARCH 		= -march=rv32i
ABI 		= -mabi=ilp32

CC		= $(TARGET)-gcc
OBJDUMP	= $(TARGET)-objdump
OBJCOPY	= $(TARGET)-objcopy
LDLIBS	 =  -lc -lgcc

COMPILER_FLAGS = -mcmodel=medany

# Use main_blinky as demo source and target file name if not specified
PROG 	?= main#firmware
CRT0	= boot.S
# Optimize for size
OPT = -Os

#WARNINGS = -Wno-shift-count-overflow -Wshadow -Wpointer-arith -Wcast-align -Werror
WARNINGS = -Werror

INCLUDES = -I.

APP_SRC = syscalls.c \
	bsp.c printf.c

ifeq ($(PROG),main)
PROG_SRC = main.c
INCLUDES += -I../../../src/include
APP_SRC += \
	../../../src/core.c \
	../../../src/common.c \
	../../../src/sense_actuate.c \
	../../../src/components/instrumentation_common.c \
	../../../src/variants/actuation_unit_generated_C.c \
	../../../src/variants/actuator_generated_C.c \
	../../../src/variants/instrumentation_handwritten_C.c \
	../../../src/variants/saturation_generated_C.c \
	../../../src/variants/instrumentation_generated_C.c
else
PROG_SRC = firmware.c
endif

ASFLAGS  += -g $(ARCH) $(ABI) -Wa,-Ilegacy
CFLAGS += $(OPT) -g3 $(ARCH) $(ABI) $(COMPILER_FLAGS) $(WARNINGS) $(INCLUDES) -DPRINTF_INCLUDE_CONFIG_H
LDFLAGS	 += -Wl,-Bstatic,-T,sections.ld,--strip-debug -nostartfiles -nostdlib $(ARCH) $(ABI)
#
# Define all object files.
#
APP_OBJ  = $(APP_SRC:.c=.o)
PROG_OBJ = $(PROG_SRC:.c=.o)
CRT0_OBJ = $(CRT0:.S=.o)
OBJS = $(CRT0_OBJ) $(PROG_OBJ) $(APP_OBJ)

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

all: firmware.elf

firmware.elf  : $(OBJS) Makefile
	@echo Linking....
	@$(CC) -o $@ $(LDFLAGS) $(OBJS) $(LDLIBS)
	@$(OBJDUMP) -S -D firmware.elf > firmware.asm
	@echo Completed $@
	@cp firmware.elf text.elf
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

