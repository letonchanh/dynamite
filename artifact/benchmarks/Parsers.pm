package Parsers;
use strict;
use warnings;
use File::Basename;
use Cwd qw/abs_path/;
use YAML::Tiny;
use Statistics::Basic;

#use File::Temp qw/ tempfile tempdir /;

our @EXPORT_OK = qw{ult find_benchmarks parse seahorn aprove expected};

sub find_benchmarks {
    my ($bdir,$bnames) = @_;
    my $scriptfn = Cwd::abs_path($0);
    my $benchdir = dirname($scriptfn)."/".$bdir;
    my @benches; my %b2expect;
    print "    Directory   : $benchdir\n";
    print "    Benchmarks  : ";
    opendir(my $dh, $benchdir) || die "Can't open $benchdir: $!";
    while (readdir $dh) {
        my $fn = $_;
        next unless $fn =~ m/\.c$/; 
        next if $fn =~ /~$/;
        $b2expect{$fn} = 'true'  if $fn =~ /-t\.c/;
        $b2expect{$fn} = 'false' if $fn =~ /-nt\.c/;
        if ($#{$bnames} > -1) {
            next unless $fn ~~ @{$bnames};
        }
        if ($bdir =~ /nla-term/) {
            next unless $fn =~ m/-both-t/;
        } elsif ($bdir =~ /termination-crafted-lit/) {
            # check to see if there is a YML file:
            my $ymlfn = "$benchdir/$fn"; $ymlfn =~ s/\.c$/\.yml/;
            #print "yamlfn: $ymlfn\n";
            if (-e $ymlfn) {
                my $expect = expected($ymlfn);
                $b2expect{$fn} = $expect;
                next if $expect eq 'IGNORE';
            }
        }
        #print "  $benchdir/$fn  (expect: $b2expect{$fn})\n";
        print " $fn (expect: $b2expect{$fn})";
        push @benches, "$fn";
    }
    closedir $dh;
    print "\n";
    return ($benchdir,\@benches,\%b2expect);
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

sub tm2str {
    my ($t) = @_;
    die "tm2str: $t\n" unless defined $t;
    return '\rUNK' if $t == -1;
    return '\rTO' if $t >= 900;
    my $out = sprintf("%0.1f", $t) if $t < 900;
    return $out;
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
    my ($time,$result) = (-1,'\rUNK');
    while (<F>) {
        $result = '\rTRUE' if /Termination result: True/;
        $result = '\rFALSE' if /Termination result: False/;
        $result = '\rFALSE' if /Non-termination result: True/;
        $result = '\rTRUE' if /Non-termination result: False/;
        $result = '\rUNK' if /Termination result: None/;
        $time   = $1 if /HARD TIMER: (\d+\.\d+)$/;
    }
    close F;
    return { time => tm2str($time), result => $result };
}

sub toTex {
    my $t = shift @_;
    $t =~ s/\*\*(\d)/^{$1} /g;
    $t =~ s/-1\*/-/g;
    $t =~ s/\*/\\cdot /g;
    $t =~ s/%/\\%/g;
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

sub dynDetailTNT {
    my ($tmpb,$logfn,$timedout,$overallt,$overallr,$expectedTNT) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my $d = { allt => tm2str($overallt), allr => $overallr,
              guessr => '\rUNK', validr => '\rUNK', conclusion => '\rUNK',
              guesst => '--', validt => tm2str(-1), rf => '', switches => 0 };
    my $TNTs;
    while(<F>) {
        if (/postorder\_vloop\_ids: \[([^\]]*)\]$/) {
            # 'vloop\_25', 'vloop\_32'
            my @lids = split ',', $1;
            $d->{loops} = 1+$#lids;
        }
        # count switches
        if (/Proving Termination: vloop_(\d+)$/) {
            my $loopid = $1;
            $d->{switches} += 1 if defined $TNTs->{$loopid}->{NT}; # == 1;
            $TNTs->{$loopid}->{T} = 1;
        } elsif (/Proving Non-Termination: vloop_(\d+)$/) {
            my $loopid = $1;
            $d->{switches} += 1 if defined $TNTs->{$loopid}->{T}; # == 1;
            $TNTs->{$loopid}->{NT} = 1;
            #analysis:1171:DEBUG (prove) - Proving Termination: vloop\_32
            #analysis:1179:DEBUG (prove) - Proving Non-Termination: vloop\_32
        }

        $d->{conclusion} = 'T' if /TNT result: True/;
        $d->{conclusion} = 'NT' if /TNT result: False/;
        $d->{conclusion} = 'NT' if /TNT result: \(False/;
        $d->{rf} = toTex($1) if /TNT result: \(False, \('vloop_\d+', \[([^\]]*)\]/; #  ZConj({-6 <= 6*n + -1*z}), [])]))/

        $d->{rf} .= toTex($1) if /ranking_function_list: \[([^\]]+)\]/;
        $d->{rfQ} = '\gRF'    if /ranking_function_list: \[([^\]]+)\]/;
        $d->{rf} .= toTex($1) if /\(simplified\) rcs: (.*)$/;
        $d->{rsQ} = '\gRS'    if /\(simplified\) rcs: (.*)$/;
        $d->{guesst} = tm2str($1) if /infer_ranking_functions: ((\d)*\.\d+)s/;
        $d->{guesst} = tm2str(($1/1000)) if /^strengthen: ((\d)*\.\d+)ms/;
    }
    $overallt = '\rTO' if $overallt == 400.0;
    $d->{switches} = '--' unless $d->{switches} > 0;
    my $str = sprintf("\\texttt{%-10s} & %-5s & %-3s & \$%-42s\$ & %-8s  \\\\ \n", # & %-5s & %10s & %-5s & %10s
                      $tmpb,
                      $expectedTNT, $d->{conclusion},
                      $d->{rf}, $overallt);
    my $strconcise = sprintf("\\texttt{%-10s} & %s & %-2s & %-4s & %2s & %-8s & %6s \\\\ \n",
                             $tmpb,
                             $d->{loops},
                             $expectedTNT,
                             $d->{rfQ}||$d->{rsQ}||'--',
                             #$d->{guesst},
                             $d->{switches},
                             $d->{conclusion},
                             $overallt);
    return ($d,$str,$strconcise);
}

sub dynDetail {
    my ($tmpb,$logfn,$timedout,$overallt,$overallr,$nonterm) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my $d = { allt => tm2str($overallt), allr => $overallr,
              guessr => '\rUNK', validr => '\rUNK',
              guesst => tm2str(-1), validt => tm2str(-1) };
    while(<F>) {
        ### PARSE RANKING FUNCTION DATA
        $d->{validt} = tm2str($1) if /validate_ranking_functions: ((\d)*\.\d+)s/;
        $d->{guesst} = tm2str($1) if /infer_ranking_functions: ((\d)*\.\d+)s/;
        $d->{validr} = '\rTRUE' if /Termination result: True/;
        $d->{validr} = '\rFALSE' if /Termination result: False/;
        $d->{validr} = '\rUNK' if /Termination result: None/;
        if(/ranking_function_list: \[([^\]]+)\]/) {
            $d->{guessr} = '\rTRUE';
            $d->{rf} = toTex($1);
            $d->{conclusion} = 'T';
        }
        ### PARSE RECURRENT SET DATA
        $d->{validr} = '\rFALSE' if /Non-termination result: True/;
        $d->{validr} = '\rTRUE' if /Non-termination result: False/;
        if(/\(simplified\) rcs: (.*)$/) { # -1 == x*z + -1*x + -1*y)
            $d->{guessr} = '\rTRUE';
            $d->{rf} = toTex($1);
            $d->{conclusion} = 'NT';
        }
        $d->{validt} = tm2str($1) if /^verify: ((\d)*\.\d+)s/;
        $d->{guesst} = tm2str($1) if /^strengthen: ((\d)*\.\d+)s/;
        $d->{allt}   = tm2str($1) if /^prove: ((\d)*\.\d+)s/;
        if(/AssertionError/ or /AttributeError/) {
            $d->{$_} = '\rAF' for qw/guesst guessr validt validr allt allr/;
        }
    }
    if($timedout and $d->{validt} > 0) {
        # decide when it timed out
        if ($d->{validt} > 800) { $d->{validt} = '\rTO'; }
    }
    if ($d->{validt} > 875) { $d->{validt} = '\rTO'; }
    $d->{allr} = '\rSCD' if $nonterm and $d->{allr} eq 'FALSE';

    $logfn =~ s/^.*benchmarks//;
    $d->{allt} = '\rTO' if $d->{allt} >= 900;
    my $str = sprintf("\\texttt{%-10s} & %-10s & \$%-42s\$ & %-8s & %10s & %-5s & %10s  \\\\ \n",
                   $tmpb, $b2desc->{$tmpb}||'', $d->{rf},
                   $d->{guesst}, $d->{guessr},
                   $d->{validt}, $d->{validr});
    my $html = sprintf("<tr><td>%-10s</td><td>%-10s</td><td>%-42s</td><td>%-8s</td><td>%10s</td><td>%-5s</td><td>%10s</td></tr>\n",
                   $tmpb, $b2desc->{$tmpb}||'', $d->{rf},
                   $d->{guesst}, $d->{guessr},
                   $d->{validt}, $d->{validr});
    #$d->{allt}, $d->{allr});
    return ($d,$str,$html);
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
sub averageTimeResult {
    my (@runs) = @_;
    die "aTR: not enough runs\n" unless $#runs >= 0;
    #print Statistics::Basic::stddev(map { $_->{time} } @runs);
    # map { print Dumper($_) } @runs;
    return {
        stddev => Statistics::Basic::stddev(map { $_->{time} } @runs),
        mean   => Statistics::Basic::mean(map { $_->{time} } @runs),
        time   => Statistics::Basic::mean(map { $_->{time} } @runs),
        result => $runs[0]->{result}
    };

}
sub parse {
    my ($tool,$logfn,$iters) = @_;
    return averageTimeResult(map { dynamo($logfn.".".$_) } (1..$iters)) if $tool eq 'dynamo';
    return ult($logfn); # for now, we don't iterate on ultimate
    #return aprove($logfn)  if $tool eq 'aprove';
    #return seahorn($logfn) if $tool eq 'seahorn';
    die "parse: unknown tool: $tool\n";
}

1;
