# aegis-manifest

## Static code capability scanner

**aegis-manifest**  creates security manifests from static code scanning of ARM architecture binaries.
It requires a database of C/C++ function signatures, DBus messages, Qml script imports and their required capabilities to work.
Dependencies are standard perl libraries, GNU utilities and GCC toolchain.
Full version was shipped in the Nokia N9 SDK.

## Usage

```
Generate Aegis security manifest files for binary packages.
Manifest declares the security tokens required by the application to run
correctly. The detection of required tokens is based on static scan of
application binaries.
The tool takes install directory of a binary package as input (first
argument) and outputs a security manifest file listing the detected
capabilities (second argument).
If no arguments are supplied, the tool expects it is run inside an
armel target, working directory is source package main level directory,
and 'dpkg-buildpackage' build artifacts are located under 'debian/'. 
The tool will process the intermediate installation directories for the
packages listed in 'debian/control', and outputs a manifest file for
each package as 'debian/package-name.aegis'.
Options:
       -d       Print debug messages to stderr.
       -t PREFIX
                Path and prefix to toolchain utilities.
                ex. '-t /toolchain/path/arm-none-linux-gnueabi-'
                also environment AEGIS_TOOL_PREFIX
                Defaults to running under armel target (empty).
       -a PATH  Look for API definitions under this path.
                also environment AEGIS_API_PATH
                Default is '/usr/share/aegis-manifest-dev/api'
       -f       Force overwrite of existing Aegis manifest files.
       -h       Show this usage message. 
Arguments:
       DESTDIR  Input destination directory to scan.
       AEGIS    Output Aegis security manifest file.
```
