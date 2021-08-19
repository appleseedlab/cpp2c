TEST_DIR	:=	./tests/c_files_and_stat_files

C_FILES		:=	$(TEST_DIR)/positive_int_macros.c \
				$(TEST_DIR)/negative_int_macros.c \
				$(TEST_DIR)/simple_constant_macros.c
				

STAT_FILES :=	$(C_FILES:%.c=%.txt)

%.txt: %.c
	java superc.SuperC -preprocessorStatistics $< 2> $@

test: $(C_FILES) $(STAT_FILES)
	python3 -m unittest discover -s=./tests

clean_stat_files:
	rm -fr $(STAT_FILES)