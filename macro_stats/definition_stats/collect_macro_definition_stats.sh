# Seems to work!
# Ignores binary files

# Object-like macros whose body is empty
NUM_OBJECT_LIKE_NO_BODY=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)[ \t]*(?<!\()(?:$|\/\/|\/\*)" $1 | wc -l)

# Obejct-like macros whose body is an integer
NUM_OBJECT_LIKE_INTEGER=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)[ \t]+\d+\s*(?:$|\/\/|\/\*)" $1 | wc -l)

# Obejct-like macros whose body is not empty and not an integer
NUM_OBJECT_LIKE_NON_INTEGER=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)[ \t](?![ \t]*(?:\d+\s*(?:$|\/\/|\/\*)|(?:[ \t]*(?:$|\/\/|\/\*))))" $1 | wc -l)

# All object-like macros
NUM_OBJECT_LIKE=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)(?:(?:$|[ \t]+|\/\/|\/\/*).*)" $1 | wc -l)

# Function-like macros whose body is empty
NUM_FUNCTION_LIKE_NO_BODY=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)\(\s*(?:[_a-zA-Z][_a-zA-Z0-9]*(?:\s*,\s*[_a-zA-Z][_a-zA-Z0-9]*)*\s*)?\)[ \t]*(?<!\()(?:$|\/\/|\/\*)" $1 | wc -l)

# Function-like macros whose body is an integer
NUM_FUNCTION_LIKE_INTEGER=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)\(\s*(?:[_a-zA-Z][_a-zA-Z0-9]*(?:\s*,\s*[_a-zA-Z][_a-zA-Z0-9]*)*\s*)?\)[ \t]*\d+\s*(?:$|\/\/|\/\*)" $1 | wc -l)

# Function-like macros whose body is not empty and not an integer
# Note that we don't need a space after the closing paren for formals
NUM_FUNCTION_LIKE_NON_INTEGER=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)\(\s*(?:[_a-zA-Z][_a-zA-Z0-9]*(?:\s*,\s*[_a-zA-Z][_a-zA-Z0-9]*)*\s*)?\)(?![ \t]*(?:\d+\s*(?:$|\/\/|\/\*)|(?:[ \t]*(?:$|\/\/|\/\*))))" $1 | wc -l)

# All function-like macros
NUM_FUNCTION_LIKE=$(grep -PIhr "^[ \t]*#define\s+([a-zA-Z_][a-zA-Z_0-9]*)\(\s*(?:[_a-zA-Z][_a-zA-Z0-9]*(?:\s*,\s*[_a-zA-Z][_a-zA-Z0-9]*)*\s*)?\)" $1 | wc -l)

PERCENT_OBJECT_LIKE_NO_BODY=$(echo "scale=2; 100 * $NUM_OBJECT_LIKE_NO_BODY / $NUM_OBJECT_LIKE" | bc -l)
PERCENT_OBJECT_LIKE_INTEGER=$(echo "scale=2; 100 * $NUM_OBJECT_LIKE_INTEGER / $NUM_OBJECT_LIKE" | bc -l)
PERCENT_OBJECT_LIKE_NON_INTEGER=$(echo "scale=2; 100 * $NUM_OBJECT_LIKE_NON_INTEGER / $NUM_OBJECT_LIKE" | bc -l)

PERCENT_FUNCTION_LIKE_NO_BODY=$(echo "scale=2; 100 * $NUM_FUNCTION_LIKE_NO_BODY / $NUM_FUNCTION_LIKE" | bc -l)
PERCENT_FUNCTION_LIKE_INTEGER=$(echo "scale=2; 100 * $NUM_FUNCTION_LIKE_INTEGER / $NUM_FUNCTION_LIKE" | bc -l)
PERCENT_FUNCTION_LIKE_NON_INTEGER=$(echo "scale=2; 100 * $NUM_FUNCTION_LIKE_NON_INTEGER / $NUM_FUNCTION_LIKE" | bc -l)

# expr $NUM_OBJECT_LIKE - $NUM_OBJECT_LIKE_NO_BODY - $NUM_OBJECT_LIKE_INTEGER - $NUM_OBJECT_LIKE_NON_INTEGER

echo "Macro Type, Body Content, Count, Percentage of Total"
echo "object-like, empty, $NUM_OBJECT_LIKE_NO_BODY", $PERCENT_OBJECT_LIKE_NO_BODY
echo "object-like, integer, $NUM_OBJECT_LIKE_INTEGER, $PERCENT_OBJECT_LIKE_INTEGER"
echo "object-like, non-integer, $NUM_OBJECT_LIKE_NON_INTEGER, $PERCENT_OBJECT_LIKE_NON_INTEGER"
echo "object-like, anything, $NUM_OBJECT_LIKE, 100.00"
echo "function-like, empty, $NUM_FUNCTION_LIKE_NO_BODY, $PERCENT_FUNCTION_LIKE_NO_BODY"
echo "function-like, integer, $NUM_FUNCTION_LIKE_INTEGER, $PERCENT_FUNCTION_LIKE_INTEGER"
echo "function-like, non-integer, $NUM_FUNCTION_LIKE_NON_INTEGER, $PERCENT_FUNCTION_LIKE_NON_INTEGER"
echo "function-like, anything, $NUM_FUNCTION_LIKE, 100.00"

# expr $NUM_FUNCTION_LIKE - $NUM_FUNCTION_LIKE_NO_BODY - $NUM_FUNCTION_LIKE_INTEGER - $NUM_FUNCTION_LIKE_NON_INTEGER
