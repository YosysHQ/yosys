#!/usr/bin/perl -w
#
# Note: You might need to install the Verilog::VCD package using CPAN..

use strict;
use Data::Dumper;
use Verilog::VCD qw(parse_vcd list_sigs);

$| = 1;

my $from_time = -1;
my $to_time = -1;

while (1)
{
	if ($ARGV[0] eq '-f') {
		$from_time = +$ARGV[1];
		shift @ARGV;
		shift @ARGV;
		next;
	}
	if ($ARGV[0] eq '-t') {
		$to_time = +$ARGV[1];
		shift @ARGV;
		shift @ARGV;
		next;
	}
	last;
}

if ($#ARGV < 0) {
	print STDERR "\n";
	print STDERR "VCD2TXT - Convert VCD to tab-separated text file\n";
	print STDERR "\n";
	print STDERR "Usage: $0 [-f from_time] [-t to_time] input.vcd [<signal regex> ...]\n";
	print STDERR "\n";
	exit 1;
}

my $vcd = parse_vcd($ARGV[0]);

for my $node (keys $vcd) {
	for my $net (@{$vcd->{$node}->{'nets'}}) {
		my $dump_this = $#ARGV == 0;
		for (my $i = 1; $i <= $#ARGV; $i++) {
			my $regex = $ARGV[$i];
			$dump_this = 1 if ($net->{"hier"} . "." . $net->{"name"}) =~ /$regex/;
		}
		next unless $dump_this;
		my $cached_value = "";
		for my $tv (@{$vcd->{$node}->{'tv'}}) {
			$cached_value = $tv->[1], next if $from_time >= 0 and +$tv->[0] < $from_time;
			next if $to_time >= 0 and +$tv->[0] > $to_time;
			printf "%s\t%s\t%s\t%s\n", $node, $from_time, $net->{"hier"} . "." . $net->{"name"}, $cached_value
					if $cached_value ne "" and $from_time >= 0 and +$tv->[0] > $from_time;
			printf "%s\t%s\t%s\t%s\n", $node, $tv->[0], $net->{"hier"} . "." . $net->{"name"}, $tv->[1];
			$cached_value = "";
		}
	}
}

