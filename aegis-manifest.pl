#!/usr/bin/perl
#
# Copyright (C) 2010-2011 Nokia Corporation and/or its subsidiary(-ies).
# 
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public License
# version 2.1 as published by the Free Software Foundation.
# 
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, 
# MA  02110-1301  USA
#
# Contact: Juha Riihimaki <Juha.Riihimaki@nokia.com>

use strict;
use warnings;

use Getopt::Std qw/getopts/;
use File::Find qw/find/;
use Date::Format qw/time2str/;
use Digest::MD5 qw/md5_hex/;
use IPC::Open3 qw/open3/;
use IPC::Open2 qw/open2/;

package main;

# MADDE extension patched in.
# End MADDE extension.

my $SELF = "aegis-manifest";
my $VERSION = "0.20110930-1+harmattan";
my $RO_MAX = 512; # maximum string length for .rodata capture.
my $BS = 4096; # buffer size used for reads/writes

# Multiple literal strings in .rodata matches to a token
# token -> hashref { argument1 -> count, argument2 -> count, ...  }
my %MapTokenStrings;

# Multiple .rodata string match to token mapping
# string -> ref counter (elf number)
my %StringArgMatch;

# Symbols found from library
# lib -> { function -> _ , ... }
my %Symbols;

#  Function call requires token
# "lib:fun" -> [ token, ... ]
my %FunTokens;

# Function call with string literal argument requires token
# "lib:fun" -> [ "argument,token" , ...  ]
my %FunStringToken;

# Mapping from soname to library path on target
# soname -> libpath
my %SOPath;

# QtDeclarative modules to tokens
# "qmlmodule:version" -> [ token, ... ]
my %DeclToken;

# #define used in fixed arguments matching and output.
# Identifier is used in comment output instead of numeric value.
# identifier -> value
my %DefineValue;

# Function call with literal #define 'd argument to token
# "lib:fun" -> [ { token -> [ argn -> [ value -> define ] , ... ] } , ... ]
my %FunFixTokens;

# Map strings which are used in rules, used to filter unused strings
# string -> count
my %StringExpect;

# Library file section information
# lib -> { 
#	NEEDED -> [ soname , soname , ... ], 
#	SECTION -> { 
#		section -> [ addr, offset, size  ]  , 
#		... 
#	} 
# }
my %Lib;

# Helper binaries with full path
# name -> fullpath
my %Helper; 

my $DataPath; # path to API data files
my $CppFiltPid; # pid for launched c++filt

# Getopt::Std 
my %Opt;
$Getopt::Std::STANDARD_HELP_VERSION = 1;

# Getopt::Std 
sub VERSION_MESSAGE { 
	print <<END;
$SELF: version $VERSION
END
}

# Getopt::Std
sub HELP_MESSAGE {
print <<END;

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

END
}

# Remove line ending and trailing whitespace
# chomp doesn't remove cr under msys windows perl
sub rtrim {
	for (@_) { s/\s+$//; } # modify arguments in-place
}

# Remove heading and and trailing whitespace
sub trim {
	for (@_) { s/^\s+//; s/\s+$//; } # modify arguments in-place
}


# Read 2-byte value from filehandle
sub readn2 {
	my ($fh) = @_;
	read($fh, my $buf, 2) == 2 || return;
	my @a = split //,$buf;
	return (ord($a[0]) << 8 | ord($a[1]));
}

# Read 4-byte value from filehandle
sub readn4 {
	my ($fh) = @_;
	read($fh, my $buf, 4) == 4 || return;
	my @a = split //,$buf;
	return (ord($a[0]) << 24 | ord($a[1]) << 16 |
			ord($a[2]) << 8 | ord($a[3]));
}

# Return integer as 4 chars
sub outn4le {
	my ($n) = @_;
	return chr($n  & 0xFF) . chr(($n & 0xFF << 8) >> 8) . 
	   chr(($n & 0xFF << 16) >> 16) . chr(($n & 0xFF << 24) >> 24);
}

# Qt dynamic resource file is identified with 'qres' followed by 0x0001 
sub rcc_is_qres {
	my ($fh) = @_;
	seek($fh, 0, 0) || die "failed fseek: $!";
	read($fh, my $headbuf, 4);
	return (($headbuf eq 'qres' && &readn4($fh) == 1) ? 1 : 0);

}

# Read an array of file names contained in Qt dynamic resource file
sub rcc_read_names {
	my ($fh, $namesp, $count) = @_;
	my $p = 0;
	my %names;

	seek($fh, $namesp, 0) || die "$SELF: failed fseek: $!";
	
	for (my $len = &readn2($fh) ; $len != 0 ; $len = &readn2($fh)) {
		my $ip = $p; $p += 6;
		my $hash = &readn4($fh);
		my $name = "";
		while ($len-- > 0) {
			my $c = &readn2($fh); $p += 2;
			next unless defined $c && $c != ord(0);
			# capture printing ASCII chars
			$name .= chr($c) if $c >= 32 && $c < 125;
		}
		$names{$ip} = $name;
		print STDERR "$SELF: rcc: name '$name'\n" if $Opt{'D'}
	}
	return \%names;
}

# Read file structure from Qt dynamic resource file
sub rcc_read_tree {
	my ($fh, $structp, $namesp, $datap, $fn_match, $qml_match) = @_;

	# Process root node first
	seek($fh, $structp, 0) || die "$SELF: failed fseek: $!";
	my $nameoff = &readn4($fh);
	my $flags = &readn2($fh);
	my $count = &readn4($fh);
	my $childoff = &readn4($fh);

	die "rcc: flags undefined" unless defined $flags;

	# expect directory flag in root node
	unless ($flags & 2) {
		print STDERR "$SELF: rcc: expect directory flag in root node, got: '$flags'\n" 
		if $Opt{'D'};
		return;
	}

	my $names = &rcc_read_names($fh, $namesp, $count);

	# Files inside resource archive
	seek($fh, $structp + 14, 0) || die "$SELF: failed fseek: $!";
	my @files;
	for (my $n = 0 ; $n < $count ; $n++) {
		my $nameoff = &readn4($fh);
		my $flags = &readn2($fh); # 0 = noflags, 1 = compressed, 2 = dir
		my $country = &readn2($fh);
		my $lang = &readn2($fh); # lang for files, childcount for dirs
		my $start = &readn4($fh); # start address of file contents
		push @files, [ $nameoff, $flags,$start ] unless $flags & 2; # file
		$count += $lang if $flags & 2; # count of files
	}

	# Resource files
	foreach my $file (@files) {
		my ($nameoff, $flags, $start) = @{ $file };
		my $filename = $names->{$nameoff};
		next if $flags & 2; # directory
		next unless &$fn_match($filename); # file name match
		# Process compressed resources
		if ($flags & 1) { # compresed
			print STDERR "$SELF: rcc: zlib: '$filename'\n"
			if $Opt{'d'};
			&rcc_get_data_zlib($fh, $datap, $start, $qml_match);
		}
		# Process uncompressed resources
		else {
			print STDERR "$SELF: rcc: plain-text: '$filename'\n"
			if $Opt{'d'};
			&rcc_get_data($fh, $datap, $start, $qml_match);
		}
	}
}

# Match plain-text content from .rcc file
sub rcc_get_data {
	my ($fh, $datap, $start, $qml_match) = @_;

	seek($fh, $datap + $start, 0) || die "$SELF: failed fseek: $!";

	# Keep last line, in case a line was broken between buffers
	my $len = &readn4($fh);
	my $carry = "";
	do {
		$len -= read($fh, my $buf, ($len >= $BS ? $BS : $len));
		my $leftover;
		foreach my $line (split /\s*\n/,$buf) {
			if ($carry ne "") {
				&$qml_match($carry . $line);
				$carry = "";
			}
			&$qml_match($line);
			$leftover = $line;
		}
		$carry = $leftover;
	} while ($len > 0);
}

# Match zlib compressed content from .rcc file
sub rcc_get_data_zlib {
	my ($fh, $datap, $start, $qml_match) = @_;
	my $checksum = 0;

	seek($fh, $datap + $start, 0) || die "$SELF: failed fseek: $!";

	# compressed length
	my $len = &readn4($fh);
	# original file length
	my $origlen = &readn4($fh);
	# zlib header
	&readn2($fh);

	$len -= 10; # ignore header 6 bytes, tail 4 bytes

	# Open two-way pipe to decompress contents with gzip
	# Redirect stderr to sink (our checksum will be borken)
	my $GZIP_PID = open3(*Writer, *Reader, *Sink, "gzip", "-dc" );

	my @gzipheader = ( 
		0x1f, 0x8b, # magic header
		8, # deflate
		0, # flags
		0, 0, 0, 0, # modification time
		2, # extra flags
		0xff # os unknown
	);
	unless ($GZIP_PID) {
		die "$SELF: Couldn't execute gzip: $!, $?\n";
	}

	# gzip header
	print Writer map(chr, @gzipheader);

	# data
	do {
		$len -= read($fh, my $buf, ($len >= $BS ? $BS : $len));
		print Writer $buf;
	} while ($len > 0);

	# 4 bytes crc32
	print Writer &outn4le(0);

	# 4 bytes uncompressed input size 
	print Writer &outn4le($origlen);

	close(Writer);

	while (my $line = <Reader>) {
		&rtrim($line);
		&$qml_match($line);
	}

	close(Reader);
	close(Sink);
	waitpid($GZIP_PID, 0);
}

# Demangle c++ symbol
sub demangle {
	my $symbol = shift;
	# Keep c++filt running
	unless (defined $CppFiltPid) {
		$CppFiltPid = open2(*FiltReader, *FiltWriter, $Helper{'cppfilt'});
		unless ($CppFiltPid) {
			die "$SELF: Couldn't execute c++filt: $! $?\n";
		}
	}
	print FiltWriter "$symbol\n";
	$|++;
	$symbol= <FiltReader>;
	die "$SELF: Received undefined value from c++filt\n" unless $symbol;
	&rtrim($symbol);
	return $symbol;
}

# Look for 'import Module Version' lines from QML input
sub qml_match { 
	my ($line, $qml_imports) = @_;
	return unless $line;
	return unless $qml_imports;
	&trim($line);
	if ($line =~ /^import\s+(\w[\w\.]+\w+)\s+([\d\.]+)/) {
		print STDERR "$SELF: qml: import: $1 $2\n" if $Opt{'D'};
		$qml_imports->{"$1:$2"}++;
	}
}

# Match '.qml' lines files from input
sub fn_match {
	my $name = shift; 
	return 0 unless $name;
	return ($name =~ /\.qml$/ ? 1 : 0); 
}

# Look for QML data from rcc file
sub rcc_qml_imports {
	my ($rccfile, $have_qml) = @_;

	my $offset = 0;

	open (my $fh,'<', $rccfile)
	or die "$SELF: couldn't open '$rccfile' for read: $!\n";
	binmode($fh);

	# qres file header
	unless (&rcc_is_qres($fh)) {
		close $fh;
		print STDERR "$SELF: qres header not found '$rccfile'\n" 
		if $Opt{'d'};
		return;
	}

	# Identifier is followed by tree, data, names offsets
	my $structp = &readn4($fh);
	my $datap = &readn4($fh);
	my $namesp = &readn4($fh);

	unless (defined $structp && defined $datap && defined $namesp) {
		print STDERR "$SELF: rcc: no pointer found: '$rccfile\@$offset'\n" 
		if $Opt{'d'};
		close $fh;
		return;
	}

	# Match files in archive ending in .qml
	# Keep track of matching files (for error output)
	my $fn_match = sub { 
		my $file = shift;
		print STDERR "$SELF: rcc: contains: '$file'\n" if $Opt{'D'};
		&fn_match($file) && ++${$have_qml};
	};

	# Match input lines against 'import module version'
	# Adds matching lines qml_imports map given as arg.
	# "module:version" -> count
	my %qml_imports;
	my $qml_match = sub { 
		my $line = shift; 
		&qml_match($line, \%qml_imports); 
	};

	&rcc_read_tree($fh, $structp, $namesp, $datap, $fn_match, $qml_match);

	close($fh);

	return keys %qml_imports;
}

# Scan soname and library dependencies from shared object file.
sub scan_elf {
	my ($destdir, $path, $so) = @_;

	my $file = "$path/$so";

	die "$SELF: File '$so' is not readable.\n" 
	unless -r $so;

	print STDERR "$SELF: Processing binary '$file'\n" if $Opt{'d'};
	
	my $soname;

	# Read required libraries sonames from binary
	my $cmd = $Helper{'readelf'}." -d $so";
	open(my $readelf_d, '-|', "$cmd 2>&1") || die "$SELF: fail: $!\n";

	# Dynamic section at offset 0x8efc contains 24 entries:
	#   Tag        Type                         Name/Value
	#  0x00000001 (NEEDED)                     Shared library: [libc.so.6]
	#  0x0000000e (SONAME)                     Library soname: [libcrypt.so.1]
	#  ...
	while (my $line = <$readelf_d>) { 
		&rtrim($line);

		if ($line =~ /Not and ELF file - it has the wrong magic/) {
			print STDERR "$SELF: Not an elf file '$file'\n" if $Opt{'d'};
			return;
		}
		$Lib{$file} = {} unless $Lib{$file};
		$Lib{$file}->{'NEEDED'} = () unless $Lib{$file}->{'NEEDED'};
		
		my ($pad, $tag, $type, $value) = split /\s+/,$line,4;
		if ($type && $type eq '(NEEDED)' && $value =~ /\[(.+?)\]/) {
			push @{ $Lib{$file}->{'NEEDED'} }, $1;
			print STDERR "$SELF: readelf: needed: $1 "
			    . ($SOPath{$1} ? "=> " . $SOPath{$1} 
			                       : "(no tokens)" )."\n" 
			if $Opt{'D'};
		}
		elsif ($type && $type eq '(SONAME)' && $value =~ /\[(.+?)\]/) {
			$soname = $1;
			$Lib{$file}->{'SONAME'} = $1;
			print STDERR "$SELF: readelf: soname: '$1'\n" if $Opt{'D'};
		}
	}
	close $readelf_d;
	if ($? != 0) {
		print STDERR "$SELF: readelf returned error\n";
		return;
	}

	$Lib{$file}->{'SONAME'} = $file unless $Lib{$file}->{'SONAME'};

	# Read section offsets inside file from section headers
	my $cmd_sections = $Helper{'readelf'}." -S $so";
	open(my $readelf_s, '-|', "$cmd_sections 2>&1") || die "$SELF: fail: $!\n";

	# There are 27 section headers, starting at offset 0x666c:
	#
	# Section Headers:
	#   [Nr] Name              Type            Addr     Off    Size   ..
	#   [ 0]                   NULL            00000000 000000 000000 ..
	#   [ 1] .interp           PROGBITS        00008134 000134 000013 ..
	#   [ 2] .note.ABI-tag     NOTE            00008148 000148 000020 ..
	#   [ 3] .gnu.hash         GNU_HASH        00008168 000168 000514 ..
	# ...
	while (my $line = <$readelf_s>) { 
		&rtrim($line);
		# section num
		next unless length $line >= 72;
		my $nr = substr($line, 3, 2);
		next unless $nr && $nr =~ /^\d+$/;
		# name
		my $name = substr($line, 7, 16);
		$name =~ s/\s+$//;
		# address/offset/size
		my ($a,$off,$size) = split /\s+/,substr($line, 41, 22),3;
		next unless $a && $a =~ /^[\da-fA-F]+$/;
		next unless $off && $off =~ /^[\da-fA-F]+$/;
		next unless $size && $size =~ /^[\da-fA-F]+$/;

		$Lib{$file}->{'SECTION'} = () unless $Lib{$file}->{'SECTION'};
		$Lib{$file}->{'SECTION'}->{$name} = [ hex($a), hex($off), hex($size) ];
	}
	close $readelf_s;
	if ($? != 0) {
		print STDERR "$SELF: readelf returned error\n";
		return;
	}

	# T - Code section
	# W - Weak
	# U - Undefined
	my %funs = %{ &elf_sym($destdir, $path, $so, 'U', 'W', 'T' ) };

	# Filter out obsolete gcc added special functions
	$Lib{$file}->{'FUNS'} = () unless $Lib{$file}->{'FUNS'};
	foreach my $fun (keys %funs) {
		next if $fun eq '_fini' || $fun eq '_init'; 
		push @{ $Lib{$file}->{'FUNS'} }, $fun;
		print STDERR "$SELF: readelf: symbol: '$fun'\n" if $Opt{'D'};
	}
}

# Process Qt resource files wrapped into executable
sub q_register_resource {
	my ($filepath, $structp, $namesp, $datap, $have_qml) = @_;
	my $filename = (split /\//,$filepath)[-1];

	# Need to have section data to map address to position in file
	unless (defined $Lib{$filepath}->{'SECTION'}->{'.rodata'}) {
		print STDERR "$SELF: no .rodata offset for ELF file '$filename'\n"
		if $Opt{'d'}
	}
	my ($addr,$off,$size) = @{ $Lib{$filepath}->{'SECTION'}->{'.rodata'} };
	unless (defined $addr && defined $off && defined $size) {		
		print "$SELF: undefined section values in ELF file '$filename'\n"
		if $Opt{'d'};
		return;
	}
	my ($got_a, $got_off, $got_size) = @{ $Lib{$filepath}->{'SECTION'}->{'.got'} };
	unless (defined $addr && defined $off && defined $size) {
		$got_a = $got_off = $got_size = 0;
	}

	print STDERR "$SELF: qres: qRegisterResource ($structp,$namesp,$datap)\n" 
	if $Opt{'D'};

	# Adjust

	# Adjust for relocation if address outside of .rodata (compiled as library)
	if ($structp < $addr || $structp > $addr+$size
	||  $namesp < $addr || $namesp > $addr+$size
	||  $datap < $addr || $datap > $addr+$size) {
		my $gip = (0xffffffff ^ int($got_a)) + 1;
		$structp -= $gip;
		$namesp -= $gip;
		$datap -= $gip;
		print STDERR "$SELF: qres: qRegisterResource ($structp,$namesp,$datap) adjusted\n" 
		if $Opt{'D'};
	}

	# Addresses are inside .rodata segment
	if ($structp < $addr || $structp > $addr+$size
	||  $namesp < $addr || $namesp > $addr+$size
	||  $datap < $addr || $datap > $addr+$size) {
		print STDERR "$SELF: qres: resource data outside of .rodata in '$filename'\n"
		if $Opt{'d'};
		print STDERR "$SELF: qres: .rodata range: $addr .. ".($addr+$size)."\n"
		if $Opt{'d'};
		return ();
	}
	$structp = $structp - $addr + $off; 
	$namesp = $namesp - $addr + $off;
	$datap = $datap - $addr + $off;
	
	open (my $fh, '<', $filename)
	or die "$SELF: couldn't open '$filename' for read: $!\n";
	binmode($fh);

	# Match files ending in .qml, incrementing the QML files counter.
	my $fn_match = sub { 
		my $file = shift;
		&fn_match($file) && ++${$have_qml};
	};

	# Match against 'import module version', adding to qml_imports map
	my %qml_imports;
	my $qml_match = sub { 
		my $line = shift; 
		&qml_match($line, \%qml_imports); 
	};

	&rcc_read_tree($fh, $structp, $namesp, $datap, $fn_match, $qml_match);
	
	close($fh);

	return keys %qml_imports;
	
}

# Scan symbols from a shared object file using nm.
# field argument specifies which field to look for (see man nm), 
# default is T (code).
# Returns hash table symbol:so
sub elf_sym {
	my ($destdir, $path, $so, @fields) = @_;
	my $field_cmp = join('',@fields) || 'T';

	my $file = "$path/$so";
	die "$SELF: file '$so' is not readable.\n" unless -r $so;

	my %sym;

	my %req_fun; # required (undefined) symbols - currently unused

	# C++ demangling is not done here
	my $cmd = $Helper{'nm'}." -gD $so";
	open(my $nm_fun, '-|', "$cmd 2>&1") || die "$SELF: fail: $!\n";

	# Sample nm -gD output:
	#
	#          U memchr
	#          U memcmp
	# 0004bee0 T sha256_block_data_order
	# 0004bc60 T sha256_block_host_order
	my $no_sym_err = 0;
	while (my $line = <$nm_fun>) {
		&rtrim($line);

		if ($line =~ /No symbols$/) {
			print STDERR "$SELF: No symbols in file '$so'\n" if $Opt{'d'};
			$no_sym_err = 1;
			last;
		}

		$line = substr($line,9); # filter address
		my ($type, $fun) = split /\s+/,$line,2;

		# hide gcc added special functions and armel specific symbols
		next if $fun eq '_fini' || $fun eq '_init' || $fun =~ /^__aeabi/;

		$sym{$fun} = $file if index($field_cmp, $type) != -1;
	}
	close $nm_fun;
	if ($no_sym_err == 0 && $? != 0) {
		print "$SELF: nm returned error\n";
	}

	return \%sym;
}

# Return symbols used in binary as hash table: address -> symbol
sub elf_symbol_address {
	my ($filepath, $filename) = @_;

	my %sym;

	die "$SELF: file '$filename' is not readable.\n" unless -r $filename;

	my $cmd = $Helper{'readelf'}." -Wsr '$filename'";
	open(my $readelf_sym, '-|', $cmd) 
	|| die "$SELF: fail: $!\n";

	# Inside 'Symbol table' section
	my $dynsym = 0;
	# Relocation section values
	my %reloc;
	# Number of variable
	my @num;

	foreach my $line (<$readelf_sym>) { 
		&rtrim($line);

		if ($line =~ /^Symbol table/) { $dynsym = 1; next; }

		if ($dynsym == 0 && $line !~ /^[0-9a-f]{8}/) { next; } # offset
		elsif ($dynsym == 1 && $line !~ /^.{8}[0-9a-f]{8}/) { next; } # value

		# Relocation section '.rel.dyn' at offset 0x930 contains 11 entries:
		#  Offset     Info    Type                Sym. Value  Symbol's Name
		# ..
		# 000092c0  00001515 R_ARM_GLOB_DAT         00000000   stderr
		# 
		# Relocation section '.rel.plt' at offset 0x988 contains 16 entries:
		#  Offset     Info    Type                Sym. Value  Symbol's Name
		# 00009264  00000516 R_ARM_JUMP_SLOT        00000000   _ZN14QDBusInterfaceD1Ev

		if ($dynsym == 0) {
			next unless length $line >= 53;
			my $offset = hex(substr($line, 0, 8));
			my $index = hex(substr($line, 10, 6));
			my $type = substr($line, 19, 22); $type =~ s/\s+$//g;
			my $value = hex(substr($line, 42, 8));
			my $name = substr($line, 53);

			next unless $type eq 'R_ARM_JUMP_SLOT';

			push @num, $name;
			$reloc{$name} = $offset;
		}

		# Symbol table '.dynsym' contains 156 entries:
		#   Num:    Value  Size Type    Bind   Vis      Ndx Name
		#   ...
		#    13: 0000a878    60 FUNC    GLOBAL DEFAULT  UND g_strdup
		#    14: 0000a8cc   176 FUNC    GLOBAL DEFAULT  UND gnome_vfs_open

		else {
			next unless length $line >= 51;
			my $value = hex(substr($line, 8, 8));
			my $type = substr($line, 23, 8); $type =~ s/\s+$//;
			my $bind = substr($line, 31, 7); $bind =~ s/\s+$//;
			my $vis = substr($line, 38, 8); $vis =~ s/\s+$//;
			my $fun = substr($line, 51) || '';

			next unless $type eq 'FUNC';

			# Empty value, look in relocation section
			if ($value == 0 && $fun ne '') { 
				$value = $reloc{$fun} || next;
			}

			$sym{$value} = $fun;  
		}
	}; 

	close $readelf_sym;

	# Disassembly of section .plt:
	# 
	# 00000a14 <.plt>:
	#  a14:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
	#  a18:	e59fe004 	ldr	lr, [pc, #4]	; a24 <_init+0x1c>
	#  a1c:	e08fe00e 	add	lr, pc, lr
	#  a20:	e5bef008 	ldr	pc, [lr, #8]!
	#  a24:	00008834 	andeq	r8, r0, r4, lsr r8
	#  a28:	e28fc600 	add	ip, pc, #0, 12
	#  a2c:	e28cca08 	add	ip, ip, #8, 20	; 0x8000
	#  a30:	e5bcf834 	ldr	pc, [ip, #2100]!	; 0x834
	my $linenum = 0;
	my $n = 0; # current index in R_ARM_JUMP_SLOT 
	&disassemble($filename, sub {
		my ($line, $pc, $word, $instr, $arg, $comment) = @_;
		return unless ++$linenum >= 5;
		# assume .plt is in same order than R_ARM_JUMP_SLOT appeared
		if ($instr eq 'ldr') {
			my $fun = $num[$n++];
			my $p = $pc - 8;
			$sym{$p} = $fun;
		}
	}, '.plt');

	return %sym;
}

# Get strings in .rodata segment as hash table: address -> string
sub elf_rodata_str {
	my ($filepath, $filename, $matcher) = @_;

	my %ro_strings;

	# .rodata section data is needed to map address to position in file
	unless (defined $Lib{$filepath}->{'SECTION'}->{'.rodata'}) {
		print STDERR "$SELF: rodata: no .rodata offset for ELF file '$filename'\n"
		if $Opt{'d'}
	}

	# .rodata address/offset/size
	my ($ro_a,$ro_off,$ro_size) = 
			@{ $Lib{$filepath}->{'SECTION'}->{'.rodata'} };

	unless (defined $ro_a && defined $ro_off && defined $ro_size) {		
		print "$SELF: rodata: no section .rodata in ELF file '$filename'\n"
		if $Opt{'d'};
		return;
	}
	# .got section data is needed to map relative .rodata address 
	# when application is compiled as a library
	unless (defined $Lib{$filepath}->{'SECTION'}->{'.got'}) {
		print STDERR "$SELF: rodata: no .got offset for ELF file '$filename'\n"
		if $Opt{'d'}
	}

	# .got address/offset/size
	my ($got_a, $got_off, $got_size) = @{ $Lib{$filepath}->{'SECTION'}->{'.got'} };
	unless (defined $ro_a && defined $ro_off && defined $ro_size) {
		$got_a = $got_off = $got_size = 0;
	}
	open (my $fh, '<', $filename)
	or die "$SELF: rodata: couldn't open '$filename' for read: $!\n";
	binmode($fh);

	seek($fh, $ro_off, 0) || die "$SELF: failed fseek: $!";

	# Read printable strings separated by null pointer
	my $n = 0; # distance from start of buffer
	my @chars; # buffer split to characters
	my $s ; # current string
	my $a; # starting address of string
	my $ga; # .got adjusted starting address of string
	my $len = 0; # length of current string
	while ($ro_size > 0) {
		$a = $ro_a + $n; # start of string
		$ga = (0xffffffff ^ $got_a) + $a + 1; # adjusted start of string
		$s = "";
		$len = 0;
		while ($ro_size > 0) {
			if ($n % $BS == 0) {
				my $chunk = ($ro_size < $BS  ? $ro_size : $BS);
				read($fh, my $buf, $chunk) == $chunk 
				|| die "$SELF: failed read, wanted $chunk\n";
				@chars = split //,$buf;
			}
			my $c = $chars[$n++ % $BS]; $ro_size--;
			last unless defined $c && ord($c) != 0;
			next unless $len++ < $RO_MAX; # max length
			# capture printing ASCII chars
			$s .= $c if ord($c) >= 32 && ord($c) < 125;
		}
		# Address -> String
		if (defined $StringExpect{$s}) { # only store strings used in rules
			$ro_strings{$a} = $s;
			$ro_strings{$ga} = $s if $got_a > 0;
			&$matcher($filename, $s);
		}
	}

	close($fh);
	return %ro_strings;
}

# Run function given as argument for each line in objdump -d 
sub disassemble {
	my ($filename, $fun, $section) = @_;
	$section = '.text' unless $section;

	# NB#209080: objdump -d cannot disassemble stripped binaries properly
	my $cmd = $Helper{'objdump'}." -D --section $section '$filename'"; 

	open(my $objdump_d, '-|', $cmd) || die "$SELF: fail: $!\n";
	foreach my $line (<$objdump_d>) { 
		&rtrim($line);

		next if length($line) <= 20;

		my $w; # first column address width
		# ' abc:'
		if (substr($line,4,1) eq ':') { $w = 4; }    
		# '     abc:'
		elsif (substr($line,8,1) eq ':') { $w = 8; } 
		else { next; }

		my $pos = substr($line, 0, $w);
		my $word = substr($line, $w + 2, 8);
		my ($instr,$arg,$comment) = split /\t/,substr($line, $w + 12),4;

		&trim($pos);
		$pos =~ /^[0-9a-f]+$/ || next;  # only 0x0-0xf

		$comment = "" unless defined $comment;
		$comment =~ s/^; //; 

		my $pc = hex($pos); # pc in decimal

		&$fun($line, $pc, $word, $instr, $arg, $comment);
	}
	close ($objdump_d);
	if ($? != 0) {
		print STDERR "$SELF: objdump returned error: $?\n";
	}
}

# Look for matching function arguments from ELF binary disassembly.
# Parses disassembly of object code, looking out for some patterns.
# This it not a generic disassembler but rather looks for some
# special cases which we're interested in. Calls functions
# given as arguments:
#	strarg_match: const char * argument (in .rodata) function call
#	fixarg_match: const parameter function call
#	qres_match: QML import statements from static qResource data
#	string_match: match strings in file's .rodata
#   have_qml: counter for QML content found
sub elf_scan_args {
	my ($filepath, $strarg_match, $fixarg_match, $qres_match, $string_match, $have_qml) = @_;

	my $filename = (split /\//,$filepath)[-1];
	my %ro_strings = &elf_rodata_str($filepath, $filename, $string_match);
	my %elf_address = &elf_symbol_address($filepath, $filename);

	# Name of the current function
	my $fun = "";
	# Map from Listing -> Function where ref to .rodata is found
	my %ldr_proc;
	# Word address references to fixed const QString ref in .rodata
	my @qstring_ref;
	# Constant values stored in register
	my @r = (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
	# Register names as they appear in input
	my %reg = ( 'r0' => 0, 'r1' => 1, 'r2' => 2, 'r3' => 3,
	            'r4' => 4, 'r5' => 5, 'r6' => 6, 'r7' => 7,
	            'r8' => 8, 'r9' => 9, 'sl' => 10, 'fp' => 11,
	            'ip' => 12, 'sp' => 13, 'lr' => 14, 'pc' => 15 );

	# Word values Address -> Word
	my %dcd; $dcd{0} = 0;

	# Find and store pc-relative loads:
	#    bba8:       e59fc010        ldr     ip, [pc, #16]   ; bbc0 <_init+0x14c4>
	#    ....
	#    bbc0:       0000d924        andeq   sp, r0, r4, lsr #18
	#    bbc4:       0000d910        andeq   sp, r0, r0, lsl r9
	&disassemble($filename, sub {
		my ($line, $pc, $word, $instr, $arg, $comment) = @_;

		# ldr has referenced to this memory address
		# assume this address contains .dcd word
		#    bbc0:       0000d924        .. word decoded as instruction ..
		if (defined $ldr_proc{$pc}) {
			$dcd{$pc} = hex($word);
			delete $ldr_proc{$pc};
		}
		# ldr referencing to forward memory address.
		#    bba8:       e59fc010        ldr     ip, [pc, #16]   ; bbc0 <_init+0x14c4>
		if ($instr eq 'ldr') {
			$arg =~ s/[\[\]]//g;
			my ($target, $relative, $third) = split /, /,$arg;

			return unless defined $reg{$target}
				&& $relative eq 'pc'
				&& $third =~ /^#(-?\d+)/;
			my $a = $1 + 8 + $pc;
			$ldr_proc{$a}++;
		}
	});

	&disassemble($filename, sub {
		my ($line, $pc, $word, $instr, $arg, $comment) = @_;

		# ldr referencing to forward memory address.
		# fremantle toolchain produces code which does ldr+mov for
		# fixed const char* references to refer to strings in
		# rodata segment
		#
		#    bba8:       e59fc010        ldr     ip, [pc, #16]   ; bbc0 <_init+0x14c4>
		#    ....
		#    bbc0:       0000d924        andeq   sp, r0, r4, lsr #18
		#    bbc4:       0000d910        andeq   sp, r0, r0, lsl r9
		if ($instr eq 'ldr') {
			$arg =~ s/[\[\]]//g;
			my ($to, $relative, $third) = split /, /,$arg;

			# r1, [pc, #32]
			return unless defined $reg{$to}
				&& $relative eq 'pc'
				&& $third =~ /^#(-?\d+)/;

			my $a = $1 + 8 + $pc;
			my $nto = $reg{$to};
			my $value = $dcd{$a} || 0; 
			# negative value passed in DCD
			$value =  -1 - ($value ^ 0xffffffff) if $value >= 0x80000000;

			$r[$nto] = $value;
		}
		# Fixed parametres
		#    8410:       e3a00001        mov     r0, #1  ; 0x1
		#    8414:       e3a01002        mov     r1, #2  ; 0x2
		#    8418:       e3a02003        mov     r2, #3  ; 0x3
		elsif ($instr eq 'mov') {
			$arg =~ s/[\[\]]//g;
			my ($to, $val) = split /, /,$arg;

			# not interested
			return if $to eq 'fp' || $to eq 'sl' || $to eq 'sp';

			my $nto = $reg{$to};

			# r0, #1
			if ($val =~ /^#(-?\d+)/) { 
				$r[ $nto ] = $1; 
			}
			# r0, [r1]
			elsif (defined $reg{$arg}) {
				my $nfrom = $reg{$arg};
				$r[ $nto ] = $r[ $nfrom ];
			}
			$r[ $nto ] = 0 if $r[ $nto ] eq "\0";

			$r[ $nto ] = -1 - ($r[ $nto ] ^ 0xffffffff) 
			if $r[ $nto ] >= 0x80000000;

		}
		# Add fixed values to a fixed parameter
		# b298:       e2812038        add     r2, r1, #56     ; 0x38
		# b2a0:       e2813094        add     r3, r1, #148    ; 0x94
		elsif ($instr eq 'add' || $instr eq 'sub') {
			my ($to,$from,$n) = split /, /,$arg;

			# not interested
			return if $to eq 'fp' || $to eq 'sl' || $to eq 'sp';

			# Literal value
			# add r1, r2, #123
			if ($n =~ /^#(-?\d+)/) { 
				$n = $1; 
			}
			# Register value
			# e.g. lr is used to pass address:
			# add     ip, r3, lr
			elsif ($n eq 'lr' || $n =~ /^(r\d+)$/) { 
				$n = $r[ $reg{$n} ]; 
			}
			# not interested in other registers
			else { 
				return; 
			}

			my $nfrom = $reg{$from};
			my $nto = $reg{$to};

			# Register-relative
			if ($nfrom != 15) { # !pc
				$r[$nto] = $r[$nfrom] + int($n) if $instr eq 'add';
				$r[$nto] = $r[$nfrom] - int($n) if $instr eq 'sub';
			}
			# PC-relative is value of PC + 8
			elsif ($nfrom == 15) { # rn <- pc
				$r[$nto] = $pc + 8 + int($n) if $instr eq 'add';
				$r[$nto] = $pc + 8 - int($n) if $instr eq 'sub';
			}
		}
		# gcc 4.5 produces code which uses movw/movt for fixed const char * 
		# to refer to strings in rodata segment
		#
		# movw zeroes and sets lower bits
		# movt sets upper bits
		#
		#    0000:      e3080824        movw    r0, #34852      ; 0x8824
		elsif ($instr eq 'movw') {
			my ($to,$n) = split /, /,$arg;
			if ($n =~ /^#(-?\d+)/) { 
				$r[ $reg{$to} ] = $1; 
			}
		}
		elsif ($instr eq 'movt') {
			my ($to,$n) = split /, /,$arg;
			if ($n =~ /^#(-?\d+)/) { 
				$r[ $reg{$to} ] += ($1 << 16); 
			}
		}
		# Filter out function calls
		#    bbbc:       ebfffb7b        bl      a9b0 <_init+0x2b4>
		elsif ($instr  eq 'bl') {
			# Clear QString reference (use use for next function call)
			my @ex_qstring_ref = @qstring_ref; 
			@qstring_ref = ();

			my $addr = hex((split / /,$arg,2)[0]);
			$fun = $elf_address{$addr} || '';
			return unless $fun
				&& $fun ne '_ZdlPv' # operator delete(void*)
				&& $fun ne '_Znwj'; # operator new(unsigned int)

			# qRegisterResourceData registers Qt resource data
			if ($fun =~ /^_Z21qRegisterResourceData/) {
				my ($structp, $namesp, $datap) = ($r[1], $r[2], $r[3]);
				@r = (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
				my @resource_imports = &q_register_resource($filepath, 
				    $structp, $namesp, $datap, $have_qml);
				foreach my $import (@resource_imports) {
					&$qres_match($import);
				}
				return;
			}

			# Static char * to const QString helper
			if ($fun eq '_ZN7QString16fromAscii_helperEPKci' 
			|| $fun eq '_ZN7QString9fromAsciiEPKci'
			|| $fun eq '_ZN7QString17fromLatin1_helperEPKci') {
				foreach my $i (0..15) {
					my $a = $r[$i];
					# Flip negative
					$a = ((abs($a) - 1) ^ 0xffffffff) if $a < 0;
					# Keep created QString reference for next bl call
					push @qstring_ref, $a if defined $ro_strings{$a};
				}
				return;
			}

			# Matcher against fixed string in .rodata
			# QString
			foreach my $a ( @ex_qstring_ref ) { 

				# Flip negative
				$a = ((abs($a) - 1) ^ 0xffffffff) if $a < 0;

				my $str = $ro_strings{$a};
				next unless $str;

				print STDERR "$SELF: call: $fun QString('$str')\n" 
				if $Opt{'D'};

				&$strarg_match($fun, $str);
			}

			# Matcher against fixed string in .rodata
			# Plain pointer to .rodata
			foreach my $i (0..15) {
				my $a = $r[$i];
				# Flip negative
				$a = ((abs($a) - 1) ^ 0xffffffff) if $a < 0;

				my $str = $ro_strings{$a};
				next unless $str;

				print STDERR "$SELF: call: $fun ('$str')\n" 
				if $Opt{'D'};

				&$strarg_match($fun, $str);
			}

			# Matcher against #define'd arguments, example:
			# socket (_,SOCK_RAW)
			&$fixarg_match($fun, ( $r[0], $r[1], $r[2], $r[3] ));
		}
		elsif ($instr eq 'bne' || $instr eq 'b' || 
				$instr eq 'blx' || $instr eq 'blt') {
			@qstring_ref = (); # Clear QString reference 
		}
	});
}

sub usage {
	die "Usage: $SELF [-d] [-t PATH] [-a PATH] [-f] [-h] DESTDIR AEGIS\n";
}

sub have_prog {
	my $prog = shift;
	my $which = (($prog =~ /^\// && $prog) || `which '$prog'`); 
	&rtrim($which);

	return $which if -x $which;
	return undef;
}

# Guess package build directory
sub package_tmpdir {
	my ($package) = @_;

	# Backward compability with debian/tmp
	return "debian/tmp" if ( -d "debian/tmp" && ! -d "debian/$package" );
	return "debian/$package";
}

# Read listed binaries in debian/control
sub packages {
	my @package;

	open my $control, '<', 'debian/control' 
	|| die "$SELF: Couldn't read 'debian/control'\n";

	foreach my $line (<$control>) {
		&rtrim($line);

		if ($line =~ /^Package:\s+?(\S+?)\s*$/) {
			push @package, $1;
		}
	}
	close $control;
	return @package;
}

# Read lines in file, calling fun for each line.
sub read_file {
	my ($file, $fun) = @_;
	die "$SELF: file '$file' is not readable.\n" unless -r $file;

	open(my $csv, '<', $file) || die "$SELF: fail: $!\n"; 

	while (my $line = <$csv>) {
		&rtrim($line);
		&$fun($line);
	}
	close $csv;
}

# Read defined functions and required tokens from text databases
sub read_database {
	my $n = 0;

	# Read object soname to library path mapping, always required
	&read_file("$DataPath/api_lib.csv", sub {
		my ($soname, $lib) = split /,/,shift,2;
		return unless $soname && $lib;
		$SOPath{$soname} = $lib;
	});

	# Read multiple .rodata string match to token mapping
	&read_file("$DataPath/api_str_token.csv", sub {
		my (@a) = split /,/,shift;
		my $token = pop @a;
		return unless scalar @a >= 1 && $token;
		my $val = { map { substr($_, 0, $RO_MAX) => -1 } @a };
		push @{ $MapTokenStrings{$token} }, $val;
		# Keep references in helper hash table
		# Count matches in current file
		foreach my $rodata (keys %{ $val }) {
			push @{ $StringArgMatch{$rodata} }, \$val->{$rodata};
			$StringExpect{$rodata}++;
		}
		++$n;
	}) 
	if -r "$DataPath/api_str_token.csv"; 

	# Read functions to token mapping
	&read_file("$DataPath/api_fun_token.csv", sub {
		my ($lib,$fun,$token) = split /,/,shift,3;
		return unless $lib && $fun && $token;
		$Symbols{$lib}->{$fun}++;
		push @{ $FunTokens{"$lib:$fun"} }, $token;
		++$n;
	}) 
	if -r "$DataPath/api_fun_token.csv";

	# Read fixed string argument to token mapping
	&read_file("$DataPath/api_fun_strarg_token.csv", sub {
		my ($lib,$fun,$token,$arg) = split /,/,shift,4;
		return unless $lib && $fun && $token && $arg;
		$Symbols{$lib}->{$fun}++;
		$StringExpect{$arg}++;
		push @{ $FunStringToken{"$lib:$fun"} }, "$token,$arg";
		++$n;
	}) 
	if -r "$DataPath/api_fun_strarg_token.csv";

	# Read #define identifier to value
	&read_file("$DataPath/api_define.csv", sub {
		my ($define,$value) = split /,/,shift;
		return unless $define =~ /^[A-Za-z_][A-Za-z0-9_]*$/;
		return unless $value =~ /^\d+$/;
		$DefineValue{$define} = $value;
	}) 
	if -r "$DataPath/api_define.csv";
	
	# Read fixed #define'd arguments to token mapping
	&read_file("$DataPath/api_fun_fixarg_token.csv", sub {
		# /lib/libc.so.6,setsockopt,CAP::net_admin,_,SOL_SOCKET,SO_DEBUG,_,_
		my ($lib,$fun,$token,@args) = split /,/,shift;
		return unless $lib && $fun && $token;
		$Symbols{$lib}->{$fun}++;
		my %argval;
		for my $i (0 .. $#args) {
			my $define = $args[$i];
			next if $define eq '_';
			$argval{ $i + 1}  = { $DefineValue{$define} => $define };
		}
		push @{ $FunFixTokens{"$lib:$fun"} }, 
				[ $token =>  { %argval } ];
	}) 
	if -r "$DataPath/api_fun_fixarg_token.csv";

	# Read QtDeclarative module to token mapping
	&read_file("$DataPath/api_declarative.csv", sub {
		my ($module,$version,$token) = split /,/,shift,3;
		return unless $module && $version && $token;
		# Importing an entire namespace should add all tokens used
		do {
			push @{ $DeclToken{"$module:$version"} }, $token;
		} while ($module =~ s/^(.+)\.[^\.]+$/$1/);
	}) 
	if -r "$DataPath/api_declarative.csv";

	return $n;
}

# Look for ELF 32-bit arm signature in file
sub has_elf_magic {
	my ($filename) = @_;

	my $buf;
	open (my $elf,'<', $filename) 
	or die "$SELF: couldn't open '$filename' for read: $!\n";
	binmode($elf);
	read($elf, $buf, 0x20, 0);
	close $elf;

	my @head = split //,$buf;

	# Don't check for executable bit set in headers since
	# booster launched binaries are built as shared objects.
	return (scalar @head >= 0x20
		&& ord($head[0]) == 0x7f && substr($buf,1,3) eq 'ELF' # elf
		&& ord($head[4]) == 0x01 # 32 bit 
		&& ord($head[18]) == 0x28 # arm
	);
}

# Scan import statements from QML file
sub qml_find_imports {
	my ($filename) = @_;

	open (my $qml,'<', $filename) 
	or die "$SELF: couldn't open '$filename' for read: $!\n";

	my @imports;

	while (my $line = <$qml>) {
		&trim($line);
		if ($line =~ /^import (\w[\w\.]+\w+) ([\d\.]+)/) {
			push @imports, "$1:$2";
		}
	}

	close $qml;
	
	return @imports;
}

# Process binaries in destdir outputting Aegis manifest to aegis_file 
# destdir: installation path (root directory) for package files
# aegis_file: target aegis manifest file
sub produce_aegis {
	my ($destdir, $aegis_file) = @_;

	my %required;

	die "$SELF: Build directory '$destdir' not accessible.\n" 
	unless -d $destdir;

	# Empty (zero-length) Aegis manifest file will result in not
	# creating/updating the manifest, and also dpkg-gencontrol will skip it
	if ( -r $aegis_file && -z $aegis_file ) {
		print "$SELF: Empty (zero-length) Aegis file found, skipped.\n";
		return;
	}

	print STDERR "$SELF: Processing build directory '$destdir'\n" if $Opt{'d'};

	my $pretty_file = (split /\//,$aegis_file)[-1];
	my $pretty_dir = (split /\//,$destdir)[-1];

	# Compare md5sum in existing version
	if (-r $aegis_file && !$Opt{'f'}) {
		open my $aegis_file_old,'<',$aegis_file;
		my $seg = 0;
		my $md5sum_cmp = "";
		my $aegis_old = "";
		while (my $line = <$aegis_file_old>) {
			&rtrim($line);
			if ($line =~ /^\<!-- modified-checksum:([0-9a-f]{32}) --\>$/) {
				$md5sum_cmp = $1;
				next;
			}
			$seg = 1 if $line =~ /^<aegis>$/;
			# compare contents until EOF
			$aegis_old .= $line if $seg; 
		}
		close $aegis_file_old;
		if ($md5sum_cmp eq "") {
			print STDERR <<END;
$SELF: No checksum found in '$pretty_file'.
$SELF: The manifest file was most likely not generated by this tool.
$SELF: This file will be placed to the resulting archive as-is.
$SELF: Run 'aegis-manifest -f' to force overwrite.
END
			return;
		}
		my $md5sum_old = md5_hex($aegis_old);
		if ($md5sum_old ne $md5sum_cmp) {
			print STDERR <<END;
$SELF: No checksum match in '$pretty_file'.
$SELF: The manifest contains manual edits to generated contents.
$SELF: This file will be placed to the resulting archive as-is.
$SELF: Run 'aegis-manifest -f' to force overwrite.\n";
END
			return;
		}
	}

	# Counter for import statements found from QML content
	# module:version -> counter
	my %qml_imports;
	# Counter for QDeclarativeEngine or QDeclarativeView
	my $have_qdecl = 0;
	# Counter for QML Files
	my $have_qml = 0;

	# Last file num which contained a string matche
	my $have_str = -1;

	# Counter of current file num for matching strings in .rodata
	my $elf_count = 0;

	# Find all QML files under package destdir
	File::Find::find({wanted => sub {
		my ($dev,$ino,$mode,$nlink,$uid,$gid);
		if ((($dev,$ino,$mode,$nlink,$uid,$gid) = lstat($_)) 
				&& -f $_ ) {
			return if $File::Find::dir =~ /\/DEBIAN/;
			my $path = $File::Find::dir;
			$path = substr($path,length($destdir)); # remove destdir
			my $filename = $path.'/'.$_;
			$filename =~ s/\/\//\//g;

			return unless $filename =~ /\.qml$/;

			print STDERR "$SELF: Processing QML file '$filename'\n" 
			if $Opt{'d'};

			++$have_qml;

			foreach my $import (&qml_find_imports($_)) {
				++$qml_imports{$import};
			}
		}
	}}, $destdir);

	# QML content from Qt resource files
	File::Find::find({wanted => sub {
		my ($dev,$ino,$mode,$nlink,$uid,$gid);
		if ((($dev,$ino,$mode,$nlink,$uid,$gid) = lstat($_)) 
				&& -f $_ ) {
			return if $File::Find::dir =~ /\/DEBIAN/;
			my $path = $File::Find::dir;
			$path = substr($path,length($destdir)); # remove destdir
			my $filename = $path.'/'.$_;
			$filename =~ s/\/\//\//g;

			return unless $filename =~ /\.rcc$/;

			print STDERR "$SELF: Processing qres rcc file '$filename'\n" 
			if $Opt{'d'};

			foreach my $import (&rcc_qml_imports($_, \$have_qml)) {
				++$qml_imports{$import};
			}
		}
	}}, $destdir);

	# Find all executables under package destdir
	File::Find::find({wanted => sub {
		my ($dev,$ino,$mode,$nlink,$uid,$gid);
		if ((($dev,$ino,$mode,$nlink,$uid,$gid) = lstat($_)) 
				&& -f $_ ) {
			return if $File::Find::dir =~ /\/DEBIAN/;
			my $path = $File::Find::dir;
			$path = substr($path,length($destdir)); # remove destdir
			my $filename = $path.'/'.$_;
			$filename =~ s/\/\//\//g;

			return unless &has_elf_magic($_);

			++$elf_count;
			&scan_elf($destdir, $path, $_);
	
			# Booster launched applications are built as so's.
			# Look for 'main' from all ELF objects.
			return unless (scalar (grep { /^(?:__libc_start_)?main$/ } 
				@{ $Lib{$filename}->{'FUNS'} }) > 0);

			# fun -> lib	
			my %have_fun;

			# Scan for matching function arguments for ELF binary
			my %elf_args_match;

			# Compare lib:fun to cases requiring token.
			SONAME: foreach my $soname (@{ $Lib{$filename}->{'NEEDED'} }) {
				my $lib = $SOPath{$soname};
				warn "$SELF: Library not found for '$soname'\n" && next 
				unless $lib;

				# Store required tokens as:
				# filename -> { token -> [ lib:fun, ... ] }
				FUN: foreach my $fun ( keys %{ $Symbols{$lib} } ) {
					my $key = "$lib:$fun";

					# API function in linked library requires token 
					# first see if it is included in our program
					my $n = 0;
					foreach my $called_fun (@{ $Lib{$filename}->{'FUNS'} }) {
						$n++ if $fun eq $called_fun;
					}
					next FUN if $n == 0;

					# function requires token
					foreach my $token ( @{ $FunTokens{$key} } )  {
						push @{ $required{$filename}->{$token} }, $key;
					}
				}

				# Construct helper hash table for matching function arguments
				foreach my $fun ( keys %{ $Symbols{$lib} } ) {
					my $key = "$lib:$fun";

					# function with string argument requires token
					foreach my $arg (@{ $FunStringToken{$key} } )  {
						my ($token,$param) = split /,/,$arg,2;
						$elf_args_match{$fun.":".$param} = $key.":".$token;
					}

					$have_fun{$fun} = $lib;
				}
			}

			# Make a copy of QML imports so they are not inherited elsewhere
			my %qml_imports_this = ( %qml_imports );

			# Parse disassembly of the ELF binary
			&elf_scan_args($filename, 
				# const char * argument (in .rodata) function call
				sub { 
					my ($fun, $arg) = @_;  
					if ($elf_args_match{$fun.":".$arg}) {
						my ($lib,$funname,$token) = 
								split /:/,$elf_args_match{$fun.":".$arg},3;
						push @{ $required{$filename}->{$token} }, # token
								$lib.":".$fun." ('".$arg."')"; # descr
					}
				},
				# const parameter function call
				sub {
					my ($callfun, @args) = @_;
					my $lib = $have_fun{$callfun} || return;

					return unless scalar @args > 0;
					return unless defined $FunFixTokens{"$lib:$callfun"};

					print STDERR "$SELF: fixarg: $callfun (".(join ',',@args).")\n" 
					if $Opt{'D'};

					foreach my $cap_args (@{ $FunFixTokens{"$lib:$callfun"} }) {
						my $cap = @{ $cap_args }[0];
						my $cmp = @{ $cap_args }[1];
						# Matching parametres with symbolic #define values
						my @matched_params; 
						for my $i (0 .. $#args) {
							$matched_params[$i] = '_';
						}
						# Try to match all parameters
						# replace matching parameters with '#define' key
						my $matches = 0;
						foreach my $argn (keys %{ $cmp }) {
							next unless defined $args[$argn - 1] && $args[$argn - 1] ne '';
							my ($value,$define) = %{ $cmp->{$argn} };
							next unless $args[$argn - 1] eq $value;
							$matched_params[$argn - 1] = $define;
							++$matches;
						}
						# Trim leftover params
						while ($#matched_params >= 0) {
							if ($matched_params[$#matched_params] eq '_') { 
								$#matched_params-- 
							}
							else { last; }
						}
						next unless $matches == scalar keys %{ $cmp };

						# Don't output multiple lines if the same match appeared
						# TODO Keep hash table of matches
						my $desc = $lib.":".$callfun.
							" (".  join (',',@matched_params) .")";
						foreach my $found (@{ $required{$filename}->{$cap} }) {
							return if $found eq $desc;
						}

						push @{ $required{$filename}->{$cap} }, $desc;
					}
				},
				#  QML import statements from static qResource data
				sub {
					my ($import) = @_;  
					++$qml_imports_this{$import};
				},
				# Strings in .rodata
				sub {
					my ($x, $rodata) = @_;
					$rodata = substr($rodata, 0, $RO_MAX); 
					return unless defined $StringArgMatch{$rodata};
					foreach my $v (@{ $StringArgMatch{$rodata} }) {
						$have_str = $elf_count; # trigger matching rules
						$$v = $elf_count 
					}
				},
				\$have_qml
			); # elf_scan_args

			# Strings found in .rodata to tokens
			foreach my $cap (keys %MapTokenStrings) {
				last unless $have_str == $elf_count;
				foreach my $ruleset ($MapTokenStrings{$cap}) {
					RULE: foreach my $rule ( @{ $ruleset } ) {
						foreach my $key ( keys %{ $rule } ) {
							next RULE unless $rule->{$key} == $elf_count;
						}

						# Add token for application, filtering duplicates
						my $desc = "strings '" . (join "','",sort keys %{ $rule }) . "'";

						foreach my $found (@{ $required{$filename}->{$cap} }) {
							next RULE if $found eq $desc;
						}

						$have_str = $elf_count;
						push @{ $required{$filename}->{$cap} }, $desc;
					}
				}
			}

			# Application contains _ZN18QDeclarativeEngine or 
			# _ZN16QDeclarativeView and thus loads QML code.
			# Inherit all tokens found from QML files imports.
			if ((scalar (grep { /^_Z..?18QDeclarativeEngine/ }
					@{ $Lib{$filename}->{'FUNS'} } ) > 0 )
			|| (scalar (grep { /^_Z..?16QDeclarativeView/ }
					@{ $Lib{$filename}->{'FUNS'} } ) > 0 )) {
				
				# Output token for QtDeclarative modules requiring itthem
				foreach my $import (sort keys %qml_imports_this) {
					my ($module,$version) = split /:/,$import,2;
					# Each import module to required token
					foreach my $token ( @{ $DeclToken{$import} } ) {
						push @{ $required{$filename}->{$token} }, # token
							"import $module $version"; # description
					}
				}
				++$have_qdecl;
			}
		} # if
	}}, $destdir); # &wanted

	print STDERR "$SELF: Found total of $have_qml QML files.\n"
	if $have_qml > 0 && $Opt{'d'};

	# QDeclarativeView or QDeclarativeEngine were found, but no QML content
	if ($have_qdecl > 0 && $have_qml == 0) {
		print STDERR "$SELF: QtDeclarative used, but could not detect QML content.\n";
	}

	# QML content was found, but no QDeclarativeView or QDeclarativeEngine
	if ($have_qdecl == 0 && $have_qml > 0) {
		print STDERR "$SELF: Could not find QtDeclarative to match QML content.\n";
	}

	# Specification requires that manifest should have content
	# Remove output file if no request sections were found
	if (scalar keys %required == 0) {
		print STDERR "$SELF: No findings in '$pretty_dir'.\n";
		if (-r $aegis_file) {
			print STDERR "$SELF: Removing '$pretty_file'.\n";
			unlink($aegis_file)
			or die "$SELF: Couldn't remove existing manifest: $!.\n";
		}
		return; # exit without output
	}

	# Update existing manifest
	print STDERR "$SELF: ".( !$Opt{'f'} ? "Updating" : "Overwriting" ) 
			. " '$pretty_file'.\n" 
	if -r $aegis_file;

	# New file
	print STDERR "$SELF: Creating '$pretty_file'.\n" 
	unless -r $aegis_file;

	my $aegis_out = "<aegis>\n";
	my $n = 0;

	# Print out Aegis <request> section for each binary
	foreach my $bin (sort keys %required) { # sort is to limit unnecessary diffs
		$aegis_out .= "\t<request policy=\"add\">\n";

		# Show warning for QML files imports
		if ((scalar (grep { /^_Z..?18QDeclarativeEngine/ }
				@{ $Lib{$bin}->{'FUNS'} } ) > 0 )
		|| (scalar (grep { /^_Z..?16QDeclarativeView/ }
				@{ $Lib{$bin}->{'FUNS'} } ) > 0 )) {

			$aegis_out .= <<END;
		<!-- Application uses QtDeclarative module. -->

END
		}

		# Warning of direct DBus client functions
		if ((scalar (grep { /^dbus_/ } 
				@{ $Lib{$bin}->{'FUNS'} } ) > 0) # libdbus
		|| (scalar (grep { /^_ZN15QDBus/ } 
				@{ $Lib{$bin}->{'FUNS'} } ) > 0)) { # libQtDbus
			$aegis_out .= <<END;
		<!-- Application accesses DBus libraries directly. -->

END
		}
		# Print out required tokens based on library calls
		# Added sorts due to different implementation of perl hash tables
		# creating unnecessary delta.
		# Group credentials which were added due to same group of calls.
		my %reqs;
		foreach my $req (sort keys %{ $required{$bin} }) {
			my %seen;
			my %calls;

			foreach my $call (sort @{ $required{$bin}->{$req} } ) {
				next if $seen{$call}++;
				
				$calls{$req} .= "|".$call if defined $calls{$req};
				$calls{$req} = $call unless defined $calls{$req};
			}
			push @{ $reqs{ $calls{$req} } }, $req;
		}

		# Output requests
		foreach my $k (sort { $reqs{$a}->[0] cmp $reqs{$b}->[0] } keys %reqs) {
			my $last = "";
			foreach my $call (split /\|/, $k) { # sorted
				my $pretty = "";
				my $args = "";

				my ($lib,$fun) = split /:/,$call,2;
				($fun,$args) = split /\s+/,$fun,2 if defined $fun;

				# Demangle function with c++filt, filter arguments
				$pretty = &demangle($fun) if defined $fun;
				$pretty =~ s/(.+?)[\s\(\)].*$/$1/ if $pretty ne "";

				# Symbol rule
				if ($pretty ne "" && not defined $args) {
					my $key = "$lib:$pretty";
					next if $key eq $last;
					$last = $key;

					$aegis_out .= "\t\t<!-- $pretty -->\n";
				}
				# Symbol rule with args
				elsif ($pretty ne "" && defined $args) {
					my $key = "$lib:$pretty $args";
					next if $key eq $last;
					$last = $key;

					$aegis_out .= "\t\t<!-- $pretty $args -->\n";

				}
				# 'import module version' statement
				elsif ($last ne $lib) {
					$aegis_out .= "\t\t<!-- $lib -->\n";
					$last = $lib;
				}

			}

			foreach my $req ( @{ $reqs{$k} } ) {
				$aegis_out .= "\t\t<credential name=\"$req\" />\n";
				++$n;
			}
			$aegis_out .= "\n";
		}

		$aegis_out .= "\t\t<for path=\"$bin\" />\n";
		
		# applauncherd booster applications are instantiated
		# from MComponentCache or from MDeclarativeCache
		if ((scalar (grep { /^_ZN(?:15MComponent|17MDeclarative)Cache/ }
				@{ $Lib{$bin}->{'FUNS'} } ) > 0)) {
			$aegis_out .= "\t\t<for path=\"applauncherd-launcher::/usr/bin/applauncherd.bin\" id=\"\" />\n";
		}

		$aegis_out .= "\t</request>\n";
	}
	$aegis_out .= "</aegis>\n";

	# strip linefeeds to limit windows/unix lf problems
	my $aegis_md5 = $aegis_out;
	$aegis_md5 =~ s/\n//g;
	my $md5sum = md5_hex($aegis_md5);

	# Overwrite existing file
	open my $aegis, '>', $aegis_file;
	my $isodate = time2str("%Y-%m-%d", time);
	# FIXME aegis dpkg wrapper doesn't correctly handle XML header
	# FIXME <?xml version="1.0" encoding="UTF-8" ?>
	print $aegis <<END;
<!-- Generated by aegis-manifest $VERSION on $isodate. -->
<!-- To disable non-interactive creation of and updates to this file,
     and adding of the resulting Aegis manifest into a Debian package,
     replace this file with an empty (zero-length) file. -->
<!-- The checksum is used for detecting any manual changes of the <aegis>
     section. If the checksum is found and matches this section, file
     contents will be updated without user interaction.
     Modify the file or remove the checksum to disable this functionality. -->
<!-- modified-checksum:$md5sum -->
END
	print STDERR "$SELF: aegis: wrote '$pretty_file' with $n entries\n" 
	if $Opt{'d'};

	print $aegis $aegis_out;

	close $aegis;
}

# main

unless (getopts('Dda:ft:h', \%Opt)) {
	print STDERR "$SELF: unknown command line options.\n";
	&HELP_MESSAGE && exit 1;
}

# Show help message
(&VERSION_MESSAGE && &HELP_MESSAGE && exit 0) if $Opt{'h'};

# Higher level debug sets also lower
$Opt{'d'} = $Opt{'D'} if $Opt{'D'};

# Arguments
(&VERSION_MESSAGE && &HELP_MESSAGE && exit 1) 
unless ((-r 'debian/control' && scalar @ARGV == 0) # use control file, no args
	or scalar @ARGV == 2); # input and output arguments

# Toolchain tool prefix path
my $tool_prefix = $Opt{'t'} 
|| $ENV{'AEGIS_TOOL_PREFIX'} 
|| "";

# Toolchain pretty printing prefix for debug output
my $tool_prefix_pretty = ($tool_prefix ne '' ? " (prefix: '$tool_prefix')" 
                                             : "");

# API data path is usually the one inside the rootstrap
$DataPath = $Opt{'a'} 
|| $ENV{'AEGIS_API_PATH'} 
|| "/usr/share/aegis-manifest-dev/api"; 

# Prefix path to sysroot dir under madde (and no -a path arg given)
$DataPath = $ENV{'SYSROOT_DIR'}.'/'.$DataPath 
if defined $ENV{'SYSROOT_DIR'} && !$Opt{'a'};

# Check that we have some tools, normally provided by a toolchain
$Helper{'readelf'} = &have_prog($tool_prefix.'readelf') 
|| die "$SELF: readelf executable not found$tool_prefix_pretty.\n";

$Helper{'nm'} = &have_prog($tool_prefix.'nm') 
|| die "$SELF: nm executable not found$tool_prefix_pretty.\n";

$Helper{'objdump'} = &have_prog($tool_prefix.'objdump') 
|| die "$SELF: objdump executable not found$tool_prefix_pretty.\n";

$Helper{'cppfilt'} = &have_prog($tool_prefix.'c++filt') 
|| die "$SELF: cppfilt executable not found$tool_prefix_pretty.\n";

# Expect gzip is provided by environment 
&have_prog('gzip') 
|| die "$SELF: gzip executable not found.\n";

# Test gcc target architecture
&have_prog($tool_prefix.'gcc') 
|| die "$SELF: gcc executable not found$tool_prefix_pretty.\n";

my $gcc_cmd = $tool_prefix.'gcc -dumpmachine 2>&1';
my $gcc_version = `$gcc_cmd`;
&rtrim($gcc_version);

die "$SELF: Manifest generation requires 'arm-none-linux-gnueabi' target.\n" 
unless $gcc_version eq 'arm-none-linux-gnueabi';

# Read token definitions from rootstrap
die "$SELF: Token definitions path '$DataPath' not accessible.\n" 
unless -d $DataPath;

my $count_tokens = &read_database();
if ($count_tokens == 0) {
	print STDERR "$SELF: No token definitions found, exiting.\n";
	exit 1;
}

my $processed_destdirs = 0;

# Arguments from command line
if ($ARGV[0] && $ARGV[1]) {
	my $destdir = $ARGV[0];
	my $aegis_file = $ARGV[1];

	$destdir =~ s/\/$// unless $destdir eq '/'; # trailing /

	die "$SELF: Package destination directory '$destdir' not accessible.\n"
	unless -d $destdir;
	
	&produce_aegis($destdir, $aegis_file);
}
# No arguments given, use packages found in debian/control
else {
	foreach my $package (&packages) {
		my $destdir = &package_tmpdir($package);
		my $aegis_file = "debian/$package.aegis";
		&produce_aegis($destdir, $aegis_file);
	}
}

# clear c++filt process
close FiltWriter if defined $CppFiltPid;
close FiltReader if defined $CppFiltPid;
waitpid($CppFiltPid, 0) if defined $CppFiltPid;

# vim:tabstop=4:softtabstop=4:shiftwidth=4:noexpandtab
