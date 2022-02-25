# Empirical Data on Macro Definition Statistics


## Programs Analyzed
- [icecast-server-v2.4.3](https://downloads.xiph.org/releases/icecast/icecast-2.4.3.tar.gz)
- [perl-5.34.0](https://www.cpan.org/src/5.0/perl-5.34.0.tar.gz)
- [redis-6.2.6](https://github.com/redis/redis/archive/refs/tags/6.2.6.zip)
- [remind-03.04.01](https://dianne.skoll.ca/projects/remind/download/remind-03.04.01.tar.gz)
- [sqlite-version-3.36.0](https://github.com/sqlite/sqlite/archive/refs/tags/version-3.36.0.zip)
- [zlib-1.2.11](https://zlib.net/zlib-1.2.11.tar.gz)


## Getting Started

### Setting Up
Download and unzip all of the above programs into this directory such that
they each have their own subdirectory

### Collecting Macro Definition Statistics for All Programs
Run the script `collect_macro_definition_stats_all.sh`

### Collecting Macro Definition Statistics for a Single Program
Run the command
```bash
$ collect_macro_definition_stats.sh <PROGRAM_DIR_NAME>
```
where PROGRAM_DIR_NAME is the name of the directory containing the program
to collect macro definition statistics for