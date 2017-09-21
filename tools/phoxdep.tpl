# $State: Exp $ $Date: 2002/01/23 14:54:21 $ $Revision: 1.6 $
# To scan a PhoX file and find dependencies

sub scan_source {
  local ($source_name, $target_name) = @_;
  $modname = $target_name;
  $modname =~ s|^.*/||;
  $modname =~ s|\.ph[io]$||;
  undef(%imports);
  undef(%locals);
  $imports{prop} = 1;
  undef(@texs);
  open(SRC, $source_name) || return;
  while(<SRC>) {
    if (m/Use[^.]*[ \t\r]([^ \t\r.]*)[ \t\r]*(\.|( with))/) {
      if ($locals{$1} != 1) {
        $imports{$1} = 1;
      }
    }
    elsif (m/Import[^.]*[ \t\r]([^ \t\r.]*)[ \t\r]*(\.|( with))/) {
      if ($locals{$1} != 1) {
        $imports{$1} = 1;
      }
    }
    elsif (m/Module[ \t\r]*([^ \t\r.]*)/) {
      $locals{$1} = 1;
    }
    elsif (m/documents[ \t]*=[ \t]*(.*$)/) {
      $doc = $1;
      while ($doc=~/([^ \t\r.]+)[ \t]*(.*$)/) {
	push(@texs,$1);
        $doc = $2;
      }
    }
  }
  close(SRC);
  undef(%deps);
  foreach $modl (keys(%imports)) {
    next if ($modl eq $modname);
    $modl =~ s|\..*$||;
    if ($dep = find_path ("$modl.phx")) {
      $dep =~ s/\.phx$/.phi/;
      $deps{$dep} = 1;
    }
  }
  foreach $texl (@texs) {
    print "$modname\.$texl\.dvi: $modname\.$texl\.tex\n";
    print "$modname\.$texl\.tex: $modname\.phi\n";
    push(@alldvi,"$modname\.$texl\.dvi");
  }
  if (%deps || %mindep) {
    print "$target_name: ";
    print $mindep;
    print " ";
    $col = length($target_name) + 2;
    foreach $dep (keys(%deps)) {
      $col += length($dep) + 1;
      if ($col >= 77) {
        print "\\\n    ";
        $col = length($dep) + 5;
      }
      print $dep, " ";
    }
    print "\n";
  }
}

sub find_path {
  local ($filename) = @_;
  if (-r $filename) {
    return $filename;
  }
  foreach $dir (@path) {
    if (-r "$dir/$filename") {
      return "$dir/$filename";
    }
  }
  return 0;
}

while ($#ARGV >= 0) {
  $_ = shift(@ARGV);
  if (/^-I(.*)$/) {
    $dir = $1 ? $1 : shift(@ARGV);
    $dir =~ s|/$||;
    unshift(@path, $dir);
  }
  elsif (/^-i(.*)$/) {
    $mindep = $1 ? $1 : shift(@ARGV);
  }
  elsif (/(.*)\.phx$/) {
    scan_source ($_, "$1.phi");
    push(@all,"$1.phi");
  }
  else {
    die "Don't know what to do with $_";
  }
}

if ($#all >= 0) {
    print "all: ";
    $col = 5;
    foreach $dep (@all) {
	$col += length($dep) + 1;
	if ($col >= 77) {
	    print "\\\n    ";
	    $col = length($dep) + 5;
	}
	print $dep, " ";
    }
    print "\n";
}

if ($#alldvi >= 0) {
    print "alldvi: ";
    $col = 5;
    foreach $dep (@alldvi) {
	$col += length($dep) + 1;
	if ($col >= 77) {
	    print "\\\n    ";
	    $col = length($dep) + 5;
	}
	print $dep, " ";
    }
    print "\n";
}
