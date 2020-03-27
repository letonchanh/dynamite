package Parsers;
use strict;
use warnings;
use File::Basename;
use Cwd qw/abs_path/;
#use File::Temp qw/ tempfile tempdir /;

our @EXPORT_OK = qw{ult find_benchmarks parse};

sub find_benchmarks {
    my ($bdir) = @_;
    my $scriptfn = Cwd::abs_path($0);
    my $benchdir = dirname($scriptfn)."/".$bdir;
    my @benches;
    print "Directory: $benchdir\n";
    print "Benchmarks: ";
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
    my $line1 = <F>;
    close F;
    return { time => '99999', result => $line1 };
}
sub parse {
    my ($tool,$logfn) = @_;
    return ult($logfn) if $tool eq 'ultimate';
    return aprove($logfn) if $tool eq 'aprove';
    die "parse: unknown tool: $tool\n";
}

1;
