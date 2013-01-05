#!/usr/bin/perl -w
#
# Note: You might need to install the Verilog::VCD package using CPAN..

use strict;
use Data::Dumper;
use Verilog::VCD qw(parse_vcd list_sigs);

$| = 1;

if ($#ARGV != 1) {
	print STDERR "\n";
	print STDERR "VCDCD - Value Change Dump Change Dumper\n";
	print STDERR "\n";
	print STDERR "Usage: $0 gold.vcd gate.vcd\n";
	print STDERR "\n";
	print STDERR "Compare a known-good (gold) vcd file with a second (gate) vcd file.\n";
	print STDERR "This is not very efficient -- so use with care with large vcd files.\n";
	print STDERR "\n";
	exit 1;
}

my $fn_gold = $ARGV[0];
my $fn_gate = $ARGV[1];

print "Finding common signals..\n";
my @gold_signals = list_sigs($fn_gold);
my @gate_signals = list_sigs($fn_gate);

my %gold_signals_hash;
my %gate_signals_hash;

for (@gold_signals) {
	my $fullname = $_;
	s/(\[([0-9]+|[0-9]+:[0-9]+)\])$//;
	$gold_signals_hash{$_}->{$fullname} = 1 unless /(^|\.)_[0-9]+_/;
}

for (@gate_signals) {
	my $fullname = $_;
	s/(\[([0-9]+|[0-9]+:[0-9]+)\])$//;
	$gate_signals_hash{$_}->{$fullname} = 1 unless /(^|\.)_[0-9]+_/;
}

my @signals;
for my $net (sort keys %gold_signals_hash) {
	next unless exists $gate_signals_hash{$net};
	# next unless $net eq "tst_bench_top.i2c_top.byte_controller.bit_controller.cnt";
	my %orig_net_names;
	print "common signal: $net";
	for my $fullname (keys $gold_signals_hash{$net}) {
		$orig_net_names{$fullname} = 1;
	}
	for my $fullname (keys $gate_signals_hash{$net}) {
		$orig_net_names{$fullname} = 1;
	}
	for my $_ (sort keys %orig_net_names) {
		push @signals, $_;
		print " $1" if /(\[([0-9]+|[0-9]+:[0-9]+)\])$/;
	}
	print "\n";
}

print "Loading gold vcd data..\n";
my $vcd_gold = parse_vcd($fn_gold, {siglist => \@signals});

print "Loading gate vcd data..\n";
my $vcd_gate = parse_vcd($fn_gate, {siglist => \@signals});

# print Dumper($vcd_gold);
# print Dumper($vcd_gate);

my %times;
my $signal_maxlen = 8;
my $data_gold = { };
my $data_gate = { };

sub checklen($$)
{
	my ($net, $val) = @_;
	my $thislen = length $val;
	$thislen += $1 if $net =~ /\[([0-9]+)\]$/;
	$thislen += $1 if $net =~ /\[([0-9]+):[0-9]+\]$/;
	$signal_maxlen = $thislen if $signal_maxlen < $thislen;
}

print "Processing gold vcd data..\n";
for my $key (keys %$vcd_gold) {
	for my $net (@{$vcd_gold->{$key}->{'nets'}}) {
		my $netname = $net->{'hier'} . "." . $net->{'name'};
		for my $tv (@{$vcd_gold->{$key}->{'tv'}}) {
			my $time = int($tv->[0]);
			my $value = $tv->[1];
			checklen($netname, $value);
			$data_gold->{$time}->{$netname} = $value;
			$times{$time} = 1;
		}
	}
}

print "Processing gate vcd data..\n";
for my $key (keys %$vcd_gate) {
	for my $net (@{$vcd_gate->{$key}->{'nets'}}) {
		my $netname = $net->{'hier'} . "." . $net->{'name'};
		for my $tv (@{$vcd_gate->{$key}->{'tv'}}) {
			my $time = int($tv->[0]);
			my $value = $tv->[1];
			checklen($netname, $value);
			$data_gate->{$time}->{$netname} = $value;
			$times{$time} = 1;
		}
	}
}

my $diffcount = 0;
my %state_gold;
my %state_gate;
my %signal_sync;
my %touched_nets;

sub set_state_bit($$$$)
{
	my ($state, $net, $bit, $value) = @_;
	my @data;
	@data = split //, $state->{$net} if exists $state->{$net};
	unshift @data, "-" while $#data < $bit;
	$data[$#data - $bit] = $value;
	$state->{$net} = join "", @data;
	$signal_sync{$net} = 1 unless exists $signal_sync{$net};
	$touched_nets{$net} = 1;
}

sub set_state($$$)
{
	my ($state, $net, $value) = @_;

	if ($net =~ /(.*)\[([0-9]+)\]$/) {
		set_state_bit($state, $1, $2, $value);
		return;
	}

	if ($net =~ /(.*)\[([0-9]+):([0-9]+)\]$/) {
		my ($n, $u, $d) = ($1, $2, $3);
		my @bits = split //, $value;
		my $extbit = $bits[0] eq "1" ? "0" : $bits[0];
		unshift @bits, $extbit while $#bits < $u - $d;
		set_state_bit($state, $n, $u--, shift @bits) while $u >= $d;
		return;
	}

	$state->{$net} = $value;
	$signal_sync{$net} = 1 unless exists $signal_sync{$net};
	$touched_nets{$net} = 1;
}

sub cmp_signal($$)
{
	my ($a, $b) = @_;
	return 1 if $a eq $b;

	my @a = split //, $a;
	my @b = split //, $b;

	unshift @a, "-" while $#a < $#b;
	unshift @b, "-" while $#b < $#a;

	for (my $i = 0; $i <= $#a; $i++) {
		return 0 if $a[$i] ne "x" && $a[$i] ne $b[$i];
	}

	return 1;
}

print "Comparing vcd data..\n";
for my $time (sort { $a <=> $b } keys %times)
{
	%touched_nets = ();
	for my $net (keys %{$data_gold->{$time}}) {
		set_state(\%state_gold, $net, $data_gold->{$time}->{$net});
	}
	for my $net (keys %{$data_gate->{$time}}) {
		set_state(\%state_gate, $net, $data_gate->{$time}->{$net});
	}
	for my $net (sort keys %touched_nets) {
		my ($stgo, $stga) = ('-', '-');
		$stgo = $state_gold{$net} if exists $state_gold{$net};
		$stga = $state_gate{$net} if exists $state_gate{$net};
		if (cmp_signal($stgo, $stga)) {
			next if $signal_sync{$net};
			printf "%-10s %-20d %-*s %-*s %s\n", "<sync>", $time, $signal_maxlen, $stgo, $signal_maxlen, $stga, $net;
			$signal_sync{$net} = 1;
		} else {
			printf "\n%-10s %-20s %-*s %-*s %s\n", "count", "time", $signal_maxlen, "gold", $signal_maxlen, "gate", "net" if $diffcount++ == 0;
			printf "%-10d %-20d %-*s %-*s %s\n", $diffcount, $time, $signal_maxlen, $stgo, $signal_maxlen, $stga, $net;
			$signal_sync{$net} = 0;
		}
	}
}

print "Found $diffcount differences.\n";
exit ($diffcount > 0 ? 1 : 0);
