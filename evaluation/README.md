# Evaluation
Note: We don't transform test scripts in these projects to ensure that the
tests are consistent (i.e., the only dependent variable in our evaluation
is the source code pre and post transformation)

## Getting Started
Build Cpp2C:
1. Navigate the the `transformation_tool` directory
2. Run the script `build.sh`

## Tiny Regex
Cloned on 2022-03-17

https://github.com/kokke/tiny-regex-c/tree/2d306a5a71128853d18292e8bb85c8e745fbc9d0

Run:
```bash
$ bash evaluate-tiny-regex.sh
```
Expected results:
TODO

## Tiny Lint
Cloned on 2022-03-17

https://github.com/kokke/tiny-lint-c/tree/4de8b64c97fda3117a7ddc9895a30adb97fbae97

Run:
```bash
$ bash evaluate-tiny-regex.sh
```
Expected results:
TODO

## Tiny HMAC
Cloned on 2022-03-17

https://github.com/kokke/tiny-HMAC-c/tree/93bdfa8114a32cf25ba70cb1f0957d3bf0f180af

Run:
```bash
$ bash evaluate-tiny-HMAC.sh
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
$ bash evaluate-remind.sh
```
Expected results:
Remind: Acceptance test PASSED

<!-- ## Redis v6.2.6
Downloaded on 2022-03-18

https://github.com/redis/redis/releases/tag/6.2.6

Run:
```bash
$ bash evaluate-redis.sh
```
Expected results:
All tests should say \[ok\]. If your terminal supports color,
these should be in green and easy to see.
If all tests pass, a message will appear saying so. -->

## Lua 5.4.4
Downloaded on 2022-03-19

- [Source link](https://www.lua.org/ftp/lua-5.4.4.tar.gz)
- [Tests link](https://www.lua.org/tests/lua-5.4.4-tests.tar.gz)

Run:
```bash
$ bash evaluate-lua.sh
```
Expected results:
```
Running Lua tests...
<Lots of dots>
Two warnings will appear, both should be labeled as "expected warnings"
```