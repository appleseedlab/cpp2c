.PHONY: test clean_stat_files

TEST_DIR	:=	./tests/c_files
				
C_FILES		:=	$(TEST_DIR)/simple_constant_macros.c \
				$(TEST_DIR)/simple_function_macros.c \
				$(TEST_DIR)/macros_with_comments.c \
				$(TEST_DIR)/unary_op_macros.c \
				$(TEST_DIR)/binary_op_macros.c
				

STAT_FILES :=	$(C_FILES:%.c=%.txt)

test: $(C_FILES) $(STAT_FILES)
	pytest

%.txt: %.c
	java superc.SuperC -preprocessorStatistics $< 2> $@

stat_files: $(STAT_FILES)


clean_stat_files:
	rm -fr $(STAT_FILES)