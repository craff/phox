#!/bin/sh

# TAG=%%DOCDIR%%/tools/phox_tags.awk
TAG=`dirname $0`/phox_tags.awk
TAGSFILE=TAGS
usage="phox_etags.sh  [-o TAGSFILE] FILE1 ... FILEn"
dir=`pwd`

while getopts "o:" option
    do
	case $option in
	o)
	    TAGSFILE=$OPTARG
	    ;;
	'?')
	    echo $usage
	    exit 2
	    ;;
	esac
    done

shift $(($OPTIND - 1))



case $# in
    0)
    echo "au moins un argument, des  fichiers à tagger"
    echo $usage
    ;;
    *)  if [ -f $dir/$TAGSFILE ] ; then
	    if rm $dir/$TAGSFILE ; then
			echo "rm $dir/$TAGSFILE"
	    fi
	    touch $TAGSFILE
	fi
	for file in $* ; do
	    echo $file
	    $TAG $file >> $dir/$TAGSFILE
	    echo "$dir/$TAGSFILE created"
	done
    ;;
esac
