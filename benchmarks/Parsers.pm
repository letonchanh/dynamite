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
	next unless $fn =~ m/\.c$/; 
        next if $fn =~ /~$/;
	if ($#{$bnames} > -1) {
	    next unless $fn ~~ @{$bnames};
	}
	if ($bdir =~ /svcomp-nla-digbench/) {
	    #next unless $fn =~ m/^.*-ult-n?t\.c/;
	    #next unless $fn =~ m/\.c$/;
	    #next if $fn =~ m/-dyn/;
	    next unless $fn =~ m/-both-t/;
	} elsif ($bdir =~ /termination-crafted-lit/) {
	    # check to see if there is a YML file:
	    my $ymlfn = "$benchdir/$fn"; $ymlfn =~ s/\.c$/\.yml/;
	    #print "yamlfn: $ymlfn\n";
	    if (-e $ymlfn) {
		my $expect = expected($ymlfn);
		next if $expect eq 'IGNORE';
	    }
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

sub tm2str {
    my ($t) = @_;
    return '\rUNK' if $t == -1;
    return '\rTO' if $t >= 900;
    return sprintf("%0.1f", $t) if $t < 900;
    die "strange time: $t";
}

sub seahorn {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my ($time,$result) = (9999,'TODO');
    while(<F>) {
        chomp;
        $result = $_ if m/BRUNCH_STAT Result/;
        $time   = $1 if m/BRUNCH_STAT Termination (.*)$/;
    }
    return { time => tm2str($time), result => $result };
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
    warn "TM: $time\n";
    close F;
    return { time => tm2str($time), result => $result };
}

sub toTex { my $t = shift @_;
    $t =~ s/-1\*/-/g;
    $t =~ s/\*/\\cdot /g;
    return $t;
}

my $b2desc = {
    "cohendiv" => "int div",
        "divbin1" => "int div",
        "manna" => "int div",
        "hard" => "int div",
        "hard2" => "int div",
        "sqrt1" => "square root",
        "dijkstra1" => "square root",
        "dijkstra2" => "square root",
        "dijkstra3" => "square root",
        "dijkstra4" => "square root",
        "dijkstra5" => "square root",
        "dijkstra6" => "square root",
        "freire1" => "square root",
        "freire2" => "cubic root",
        "cohencu1" => "cubic sum",
        "cohencu2" => "cubic sum",
        "cohencu3" => "cubic sum",
        "cohencu4" => "cubic sum",
        "cohencu5" => "cubic sum",
        "cohencu6" => "cubic sum",
        "cohencu7" => "cubic sum",
        "egcd" => "gcd",
        "egcd1" => "gcd",
        "egcd2" => "gcd",
        "egcd3" => "gcd",
        "prodbin" => "gcd, lcm",
        "prod4br" => "gcd, lcm",
        "knuth" => "product",
        "fermat1" => "product",
        "fermat2" => "divisor",
        "lcm1" => "divisor",
        "lcm2" => "divisor",
        "geo1" => "geo series",
        "geo2" => "geo series",
        "geo3" => "geo series",
        "ps2" => "pow sum",
        "ps3" => "pow sum",
        "ps4" => "pow sum",
        "ps5" => "pow sum",
        "ps6" => "pow sum"
};
sub dynDetail {
    my ($tmpb,$logfn,$timedout,$overallt,$overallr) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my $d = { allt => $overallt, allr => $overallr,
              guessr => '\nparse', validr => '\nparse',
              guesst => tm2str(-1), validt => tm2str(-1) };
    while(<F>) {
        $d->{validt} = $1 if /validate_ranking_functions: ((\d)*\.\d+)s/;
        $d->{guesst} = $1 if /infer_ranking_functions: ((\d)*\.\d+)s/;
        $d->{validr} = '\rTRUE' if /Termination result: True/;
        if(/ranking_function_list: \[([^\]]+)\]/) {
            $d->{guessr} = '\rTRUE';
            $d->{rf} = toTex($1);
        }
    }
    if($timedout) {
        # decide when it timed out
        if ($d->{validt} > 800) { $d->{validt} = '\rTO'; }
    }

    $logfn =~ s/^.*benchmarks//;
    $d->{allt} = sprintf("%.2f",$d->{allt});
    $d->{allt} = '\rTO' if $d->{allt} >= 900;
    my $str = sprintf("\\texttt{%-10s} & %-10s & \$%-12s\$ & %-3.2f & %10s & %.2f & %10s & %s \\\\ \% $logfn \n",
                   $tmpb, $b2desc->{$tmpb}, $d->{rf},
                   $d->{guesst}, $d->{guessr},
                   $d->{validt}, $d->{validr},
                   $d->{allt}
        );
    return ($d,$str);
    #$tool, $tmpb, $b2res{$b}->{time}, $b2res{$b}->{result});

    # Time log:
    #gen_rand_inps: 0.141s
    #_get_traces_mp: 0.158s
    #_merge_traces: 0.121s
    #get_traces_from_inps: 0.280s
    #infer_ranking_functions: 10.530s
    #prove_reach: 16.663s
    #validate_ranking_functions: 16.807s
    #prove: 27.762s
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
    return { time => tm2str($time), result => $result };
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
