#!/usr/bin/perl
# parse 'yosys -t' logfile and find slow passes

my $max_depth = 0;
my %last_line_by_depth;
my %last_time_by_depth;

my @lines_text;
my @lines_depth;
my @lines_time;

while (<>)
{
	chomp;
	next unless /^\[([0-9.]+)\] (([0-9]+\.)+)/;
	my ($this_time, $this_id, $this_header) = ($1, $2, $4);

	push @lines_text, $_;
	push @lines_depth, 0;
	push @lines_time, 0;

	my $depth = $this_id;
	$depth =~ s/[^.]//g;
	$depth = length $depth;
	$max_depth = $depth if $depth > $max_depth;

	for (my $i = $depth; $i <= $max_depth; $i++) {
		next unless exists $last_time_by_depth{$i};
		$lines_time[$last_line_by_depth{$i}] = $this_time-$last_time_by_depth{$i};
		delete $last_time_by_depth{$i};
		delete $last_header_by_depth{$i};
	}

	$last_time_by_depth{$depth} = $this_time;
	$last_line_by_depth{$depth} = $#lines_text;
	$lines_depth[$#lines_text] = $depth;
}

for (my $depth = 1; $depth <= $max_depth; $depth++) {
	printf "\nSlow passes on recursion depth %d:\n", $depth;
	my @lines;
	for (my $i = 0; $i <= $#lines_text; $i++) {
		next if $lines_depth[$i] != $depth or $lines_time[$i] < 1.0;
		push @lines, sprintf("%3d  %08.2f  %s\n", $lines_depth[$i], $lines_time[$i], $lines_text[$i]);
	}
	for my $line (sort {$b cmp $a} @lines) {
		print $line;
	}
}

printf "\nFull journal of headers:\n";
for (my $i = 0; $i <= $#lines_text; $i++) {
	printf "%3d  %08.2f  %s\n", $lines_depth[$i], $lines_time[$i], $lines_text[$i];
}

