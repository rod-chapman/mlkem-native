# SPDX-License-Identifier: Apache-2.0
SOURCES = $(wildcard mlkem/*.c)

CPPFLAGS += -Imlkem
TESTS = test_kyber bench_kyber gen_NISTKAT gen_KAT

MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

$(MLKEM512_DIR)/bin/%: CPPFLAGS += -DKYBER_K=2
$(TESTS:%=$(MLKEM512_DIR)/bin/%512):$(MLKEM512_DIR)/bin/%512: $(MLKEM512_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM512_DIR),$(SOURCES))

$(MLKEM768_DIR)/bin/%: CPPFLAGS += -DKYBER_K=3
$(TESTS:%=$(MLKEM768_DIR)/bin/%768):$(MLKEM768_DIR)/bin/%768: $(MLKEM768_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM768_DIR),$(SOURCES))

$(MLKEM1024_DIR)/bin/%: CPPFLAGS += -DKYBER_K=4
$(TESTS:%=$(MLKEM1024_DIR)/bin/%1024):$(MLKEM1024_DIR)/bin/%1024: $(MLKEM1024_DIR)/test/%.c.o  $(call MAKE_OBJS,$(MLKEM1024_DIR),$(SOURCES))