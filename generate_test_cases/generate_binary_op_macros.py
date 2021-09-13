'''
generate_test_cases.py

Generate test cases for converting macros involving binary expressions.

Possible code smell: Tight coupling here with testing setup.
'''

hierarchy_examples = [
    ('long double', '1.0L'),
    ('double', '1.0'),
    ('unsigned long long int', '1ULL'),
    ('long long int', '1LL'),
    ('unsigned long int', '1UL'),
    ('long int', '1L'),
    ('unsigned int', '1U'),
    ('int', '1'),
    ('char', "'a'"),
]


macro_definitions = []
macro_data_collection_results = []
macro_data_classification_results = []

line_no = 1
for i, (h1, left) in enumerate(hierarchy_examples):
    for h2, right in hierarchy_examples[i:]:
        expected_type = h1
        body = f"{left} + {right}"
        name = f"IDENT{line_no}"
        definition = f"#define {name} {body} // {expected_type}"
        macro_definitions.append(definition)

        macro_data_collection_result = f"ObjectDefine(c_file, {line_no}, {line_no}, 1, 1, '{name}', \"{body}\")"
        macro_data_collection_results.append(macro_data_collection_result)
        macro_data_classification_result = f"SimpleExpressionMacro({macro_data_collection_result}, '{expected_type}', \"{body}\")"
        macro_data_classification_results.append(
            macro_data_classification_result)
        line_no += 1

print(*macro_definitions, sep="\n")

# Print using list comprehensions for proper indentation
print()
print("Expected result for macro data collection test cases:")
print("[")
[print("    " + result + ",") for result in macro_data_collection_results]
print("]")

print()
print("Expected result for macro classification test cases:")
print("[")
[print("    " + result + ",") for result in macro_data_classification_results]
print("]")
