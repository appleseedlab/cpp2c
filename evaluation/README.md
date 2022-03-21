# Evaluation
Note: We don't transform test scripts in these projects to ensure that the
tests are consistent (i.e., the only dependent variable in our evaluation
is the source code pre and post transformation)

## Getting Started
Build Cpp2C:
1. Navigate the the `implementation` directory
2. Run the script `build.sh`

## Tiny Regex
Cloned on 2022-03-17

https://github.com/kokke/tiny-regex-c/tree/2d306a5a71128853d18292e8bb85c8e745fbc9d0

Run:
```bash
$ bash evaluate-tiny-regex.sh -run-tests
```
Expected results:
TODO

## Tiny Lint
Cloned on 2022-03-17

https://github.com/kokke/tiny-lint-c/tree/4de8b64c97fda3117a7ddc9895a30adb97fbae97

Run:
```bash
$ bash evaluate-tiny-regex.sh -run-tests
```
Expected results:
TODO

## Tiny HMAC
Cloned on 2022-03-17

https://github.com/kokke/tiny-HMAC-c/tree/93bdfa8114a32cf25ba70cb1f0957d3bf0f180af

Run:
```bash
$ bash evaluate-tiny-HMAC.sh -run-tests
```
Expected results:
TODO

<!-- ## Icecast Server v2.4.3
https://github.com/xiph/Icecast-Server/releases/tag/v2.4.3 -->

## Remind v03.04.02
Downloaded on 2022-03-17

https://dianne.skoll.ca/projects/remind/

Run:
```bash
$ bash evaluate-remind.sh -run-tests
```
Expected results:
Remind: Acceptance test PASSED

## Lua 5.4.4
Downloaded on 2022-03-19

- [Source link](https://www.lua.org/ftp/lua-5.4.4.tar.gz)
- [Tests link](https://www.lua.org/tests/lua-5.4.4-tests.tar.gz)

Run:
```bash
$ bash evaluate-lua.sh -run-tests
```
Expected results:
```
Running Lua tests...
<Lots of dots>
Two warnings will appear, both should be labeled as "expected warnings"
```

## bc v1.07
Downloaded on 2022-03-20

https://mirrors.kernel.org/gnu/bc/bc-1.07.tar.gz

Run:
```bash
$ bash evaluate-bc.sh -run-tests
```
Expected results:
The output should end with a sequence of test time outputs that look like this:
```
real    0m0.xxxs
user    0m0.xxxs
sys     0m0.xxxs
```
If these test time outputs contain an error message, then something went wrong

## gzip v1.10
Downloaded on 2022-03-20

https://gnu.mirror.constant.com/gzip/gzip-1.10.tar.gz

Run:
```bash
$ bash evaluate-gzip.sh -run-tests
```
Expected results:
```
============================================================================
Testsuite summary for gzip 1.10
============================================================================
# TOTAL: 22
# PASS:  22
# SKIP:  0
# XFAIL: 0
# FAIL:  0
# XPASS: 0
# ERROR: 0
```