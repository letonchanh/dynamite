package Parsers;
use strict;
use warnings;
use File::Basename;
use Cwd qw/abs_path/;
#use File::Temp qw/ tempfile tempdir /;

our @EXPORT_OK = qw{ult find_benchmarks parse seahorn aprove};

sub find_benchmarks {
    my ($bdir) = @_;
    my $scriptfn = Cwd::abs_path($0);
    my $benchdir = dirname($scriptfn)."/".$bdir;
    my @benches;
    print "| Directory: $benchdir\n";
    print "| Benchmarks: ";
    opendir(my $dh, $benchdir) || die "Can't open $benchdir: $!";
    while (readdir $dh) {
        my $fn = $_;
        next unless $fn =~ m/^.*-ult-n?t\.c/;
        next if $fn =~ /~$/;
        print "$benchdir/$fn  ";
        push @benches, "$fn";
    }
    closedir $dh;
    print "\n";
    return ($benchdir,@benches);
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
    return { time => $time, result => $result };
}

sub ult {
    my ($logfn) = @_;
    open(F,"$logfn") or warn "file $logfn - $!";
    my ($time,$result) = ('UNKNOWN','UNKNOWN');
    while (<F>) {
        if (/TerminationAnalysisResult: Unable to decide termination/) {
            $result = '"Unable to decide termination"';
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
    die "parse: unknown tool: $tool\n";
}

1;
