#! /bin/bash
# basile
# prcsid $Id: testjit.sh,v 1.6 2004-06-21 11:20:20 basile Exp $
# prcsproj $ProjectHeader: Basile_Csl 0.183 Mon, 12 Apr 2004 14:47:45 +0200 starynke $

. _jitconfig.mk

export OCAML_TOPDIR
if [ ! -f $OCAML_TOPDIR/ocamlc ]; then
   no ocamlc in $OCAML_TOPDIR
   exit 1
fi


cristaltestdir=$OCAML_TOPDIR/test/testinterp
jitopt="-v -t"
bcopt="-t"
verbose=""
make  ocamljitrund ocamljitrun

function ocamlcompil() {
    $OCAML_TOPDIR/byterun/ocamlrun $OCAML_TOPDIR/ocamlc -I . -I $cristaltestdir -I ../stdlib -I $OCAML_TOPDIR/stdlib $*
}
function runbc() {
    time $OCAML_TOPDIR/byterun//ocamlrund $*
}
function runjit() {
    time ./ocamljitrund $*
}
function usage() {
    echo "usage: $0" 
    echo "\t[-v] #verbose"
    echo "\t[-B bytecode_opt] #bytecode option"
    echo "\t[-J jit_opt] #jitcode option"
    echo "\t[-h] #this help"
    exit 0
}

while getopts "vhB:J:" Option; do
case $Option in
    v) verbose="-v";;
    h) usage;;
    B) bcopt=$OPTARG;;
    J) jitopt=$OPTARG;;
    *) usage; exit 1;;
esac
done
shift $(($OPTIND - 1))

ocamlcompil -c $cristaltestdir/lib.ml

# limit the cputime for the jit test
ulimit -t 300

function dotest() {
    srcfile=$1
    if [ ! -f "$srcfile" ]; then
	echo missing source file $srcfile
	exit 1
    fi
    basefile=_$(basename $srcfile .ml)_
    bytefile=$basefile.byt
    instrfile=$basefile.instr
    tracefile=$basefile.trace
    jitfile=$basefile.jit 
    pervasives="-nopervasives"
    case $basefile in
	_*[012][0-9][0-9]*_) xtralibs=;;
        _*301*) xtralibs=$OCAML_TOPDIR/stdlib/stdlib.cma; pervasives="";;
        _*3[0-9][0-9]*_|*sli*) xtralibs=$OCAML_TOPDIR/stdlib/stdlib.cma;;
	*) xtralibs=;;
    esac
    rm -f core
    rm -f _test.byte _test.instr _test.ml _test.trace _test.jit
    ln -s $bytefile _test.byte
    ln -s $srcfile _test.ml
    ln -s $tracefile _test.trace
    ln -s $instrfile _test.instr
    ln -s $jitfile _test.jit
    ocamlcompil -dinstr -o $bytefile $pervasives $cristaltestdir/lib.cmo $xtralibs $srcfile >& $instrfile
    if [ $? -ne 0 ] ; then 
	echo compilation $srcfile failed
	echo with ./ocamlrun $OCAML_TOPDIR/ocamlc -I .  -I $cristaltestdir -I ../stdlib -I $OCAML_TOPDIR/stdlib  -dinstr -o $bytefile $cristaltestdir/lib.cmo $xtralibs $srcfile 
	exit 1
    fi
    echo -n testing $bytefile ': '
    runbc $bcopt $bytefile >& $tracefile
    runstat=$?
    if runjit $jitopt $bytefile >& $jitfile ; then
	echo ok
    else
	jitstat=$?
	echo failed 
	echo bytefile $bytefile failed for jit  jit status $jitstat run status $runstat
	case $bytefile in
	    *t060*) echo $bytefile expected to fail;;
	    *)	echo unexpected failure of $bytefile;
		exit 1;;
	esac
    fi
}

if [ $# -ge 1 ]; then
    for f in $*; do
	echo testing on $f
	dotest $f || (echo $f failed; exit 1)
    done
else
    for f in $cristaltestdir/t*.ml; do
	dotest $f || (echo $f failed; exit 1)
    done
fi

echo all test done
#eof $Id: testjit.sh,v 1.6 2004-06-21 11:20:20 basile Exp $