'''
generate_test_cases.py

Generate test cases for converting macros involving binary expressions
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


results = []

line_no = 1
for i, (h1, left) in enumerate(hierarchy_examples):
    for h2, right in hierarchy_examples[i:]:
        expected_type = ""
        expected_type = h1
        body = f"{left} + {right}"
        name = f"IDENT{line_no}"
        print(f"#define {name} {body} // {expected_type}")
        results.append(
            f"ObjectDefine(c_file, {line_no}, {line_no}, 1, 1, '{name}', \"{body}\"),"
        )
        line_no += 1

print()
print(*results, sep='\n')
