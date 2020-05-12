package Parsers;
use strict;
use warnings;
use File::Basename;
use Cwd qw/abs_path/;
use YAML::Tiny;
#use File::Temp qw/ tempfile tempdir /;

our @EXPORT_OK = qw{ult find_benchmarks parse seahorn aprove expected};

sub find_benchmarks {
    my ($bdir,$bnames) = @_;
    my $scriptfn = Cwd::abs_path($0);
    my $benchdir = dirname($scriptfn)."/".$bdir;
    my @benches;
    print "| Directory: $benchdir\n";
    print "| Benchmarks: ";
    opendir(my $dh, $benchdir) || die "Can't open $benchdir: $!";
    while (readdir $dh) {
        my $fn = $_;
        #next unless $fn =~ m/^.*-ult-n?t\.c/;
	#next unless $fn =~ m/\.c$/;
	#next if $fn =~ m/-dyn/;
	next unless $fn =~ m/-both-t/;
        next if $fn =~ /~$/;
	if ($#{$bnames} > -1) {
	    next unless $fn ~~ @{$bnames};
	    #use Data::Dumper;
	    #print "not skipping $fn\n".Dumper($bnames);
	}
	# check to see if there is a YML file:
	my $ymlfn = "$benchdir/$fn"; $ymlfn =~ s/\.c$/\.yml/;
	if (-e $ymlfn) {
	    #print "  found yml: $ymlfn\n";
	    #print "   checking for termination property\n";
	    my $expect = expected($ymlfn);
	    next if $expect eq 'IGNORE';
	}
        print "$benchdir/$fn  ";
        push @benches, "$fn";
    }
    closedir $dh;
    print "\n";
    return ($benchdir,@benches);
}

sub expected {
    my ($fn) = @_;
    my $yaml = YAML::Tiny->read( $fn );
    my @props = @{ $yaml->[0]->{properties} };
    foreach my $p (@props) {
	if ($p->{property_file} eq '../properties/termination.prp') {
	    return $p->{expected_verdict};
	}
    }
    #warn "could not parse $fn\n";
    return 'IGNORE';
}
my $ex = "format_version: '1.0'

# old file name: cstrlen_true-termination_true-no-overflow.c
input_files: 'cstrlen.c'

properties:
  - property_file: ../properties/no-overflow.prp
    expected_verdict: true
  - property_file: ../properties/termination.prp
  expected_verdict: true
    ";

sub seahorn {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my ($time,$result) = (9999,'TODO');
    while(<F>) {
        chomp;
        $result = $_ if m/BRUNCH_STAT Result/;
        $time   = $1 if m/BRUNCH_STAT Termination (.*)$/;
    }
    return { time => $time, result => $result };
}

sub dynamo {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my ($time,$result) = (-1,'UNK');
    while (<F>) {
        if (/Termination result: True/) {
            $result = 'TRUE';
        }
        elsif (/Termination result: False/) {
            $result = 'FALSE';
        }
        elsif (/Termination result: None/) {
            $result = 'UNKNOWN';
        }
# Time log:
#gen_rand_inps: 0.141s
#_get_traces_mp: 0.158s
#_merge_traces: 0.121s
#get_traces_from_inps: 0.280s
#infer_ranking_functions: 10.530s
#prove_reach: 16.663s
#validate_ranking_functions: 16.807s
#prove: 27.762s
        if (/EJK TIMER: (\d+(\.\d+)?)$/) {
            $time = $1;
        }
    }
    close F;
    return { time => $time, result => $result };
}

sub ult {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my ($time,$result) = (-1,'UNK');
    while (<F>) {
        if (/TerminationAnalysisResult: Unable to decide termination/) {
            #$result = '"Unable to decide termination"';
	    $result = 'UNK';
        }
        if (/RESULT: Ultimate proved your program to be correct/) {
            $result = 'TRUE';
        }
        if (/RESULT: Ultimate proved your program to be incorrect/) {
            $result = 'FALSE';
        }
        if (/OverallTime: (\d+\.\d+)s,/) {
            $time = $1;
        }
        if (/out of memory/) {
            $result = 'MEMOUT';
        }
        if (/Cannot allocate memory/) {
            $result = 'MEMOUT';
        }
        if (/BüchiAutomizer plugin needed (\d+\.\d+)s/) {
            $time = $1;
        }
    }
    close F;
    return { time => $time, result => $result };
}

sub aprove {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my $res = <F>;
    while (<F>) {
        $res = '"could not be shown"' if /Termination of the given C Problem could not be shown/;
    }
    close F;
    return { time => '99999', result => $res };
}
sub parse {
    my ($tool,$logfn) = @_;
    return ult($logfn)     if $tool eq 'ultimate';
    return aprove($logfn)  if $tool eq 'aprove';
    return seahorn($logfn) if $tool eq 'seahorn';
    return dynamo($logfn)  if $tool eq 'dynamo';
    die "parse: unknown tool: $tool\n";
}

1;
