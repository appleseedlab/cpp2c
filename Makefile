.PHONY: test

TEST_DIR	:=	./tests/c_files
				
C_FILES		:=	$(TEST_DIR)/simple_constant_macros.c \
				$(TEST_DIR)/simple_function_macros.c \
				$(TEST_DIR)/macros_with_comments.c \
				$(TEST_DIR)/unary_op_macros.c \
				$(TEST_DIR)/binary_op_macros.c
				

test: $(C_FILES)
	pytest
