TARGET=riscv64-unknown-elf
ARCH 		= -march=rv32i
ABI 		= -mabi=ilp32
CC =clang --target=riscv32
OBJDUMP	= $(TARGET)-objdump
OBJCOPY	= $(TARGET)-objcopy
LD 		= $(TARGET)-gcc
LDLIBS	 =  -lc -lgcc

COMPILER_FLAGS = -mcmodel=medany

# Use main_blinky as demo source and target file name if not specified
PROG 	?= main
CRT0	= boot.S
# Optimize for size
OPT = -Os

# NOTE: why do we have different warnings setup?
WARNINGS = -Wno-shift-op-parentheses -Wno-shift-count-overflow -Wpointer-arith -Wcast-align -Werror

INCLUDES = -I. -I/opt/riscv/riscv64-unknown-elf/include

APP_SRC = syscalls.c \
	bsp.c printf.c

ifeq ($(PROG),main)
PROG_SRC = ../../../src/rv32_main.c
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
	../../../src/variants/actuation_unit_generated_SystemVerilog.c \
	../../../src/variants/instrumentation_handwritten_SystemVerilog.c \
	../../../src/variants/instrumentation_generated_SystemVerilog.c \
	../../../src/variants/instrumentation_generated_C.c
else
PROG_SRC = firmware.c
endif

ASFLAGS  += -g $(ARCH) $(ABI) -Wa,-Ilegacy
CFLAGS += $(OPT) -g3 $(ARCH) $(ABI) $(COMPILER_FLAGS) $(WARNINGS) $(INCLUDES) -DPRINTF_INCLUDE_CONFIG_H
LDFLAGS	 += -Wl,-Bstatic,-T,sections.ld,--strip-debug -nostartfiles -nostdlib $(ARCH) $(ABI)


ifneq ($(SELF_TEST_PERIOD_SEC),)
CFLAGS += -DSELF_TEST_PERIOD_SEC=$(SELF_TEST_PERIOD_SEC)
endif

SELF_TEST ?= Enabled

ifeq ($(SELF_TEST),Enabled)
CFLAGS += -DENABLE_SELF_TEST
endif

DEBUG_PRINT ?= Disabled

ifeq ($(DEBUG_PRINT),Enabled)
CFLAGS += -DDEBUG
endif

CLEAR_SCREEN ?= Enabled
ifeq ($(CLEAR_SCREEN),Enabled)
CFLAGS += -DCLEAR_SCREEN=1
else
CFLAGS += -DCLEAR_SCREEN=0
endif

CORE_FREQ ?= 100000
CFLAGS += -DCORE_FREQ=$(CORE_FREQ)
$(info CORE_FREQ=$(CORE_FREQ))

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
	@$(LD) -o $@ $(LDFLAGS) $(OBJS) $(LDLIBS)
	@$(OBJDUMP) -S -D firmware.elf > firmware.asm
	@echo Completed $@

clean :
	@rm -f $(OBJS)
	@rm -f *.elf
	@rm -f *.asm
	@find ../../../ -iname '*.o' -exec rm -rf {} \;

