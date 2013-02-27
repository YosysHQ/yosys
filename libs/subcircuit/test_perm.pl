#!/usr/bin/perl -w

use strict;

# let "macc" implement a function like Y = (A*B) + (C*D)
#
# the following permutations of the input pins exist:
#
#   g01 | A B C D |  match
#   g02 | A B D C |  match
#   g03 | A C B D |  not
#   g04 | A C D B |  not
#   g05 | A D B C |  not
#   g06 | A D C B |  not
#   g07 | B A C D |  match
#   g08 | B A D C |  match
#   g09 | B C A D |  not
#   g10 | B C D A |  not
#   g11 | B D A C |  not
#   g12 | B D C A |  not
#   g13 | C A B D |  not
#   g14 | C A D B |  not
#   g15 | C B A D |  not
#   g16 | C B D A |  not
#   g17 | C D A B |  match
#   g18 | C D B A |  match
#   g19 | D A B C |  not
#   g20 | D A C B |  not
#   g21 | D B A C |  not
#   g22 | D B C A |  not
#   g23 | D C A B |  match
#   g24 | D C B A |  match

my @matches = qw/g01 g02 g07 g08 g17 g18 g23 g24/;
my @non_matches = qw/g03 g04 g05 g06 g09 g10 g11 g12 g13 g14 g15 g16 g19 g20 g21 g22/;

print "\n";

for my $i (0..3) {
for my $j (0..2) {
for my $k (0..1) {
	my @t = qw/A B C D/;
	print "# ";
	print splice(@t,$i,1),splice(@t,$j,1),splice(@t,$k,1),$t[0];
	print "\n";
}}}

print "\n";

my $iter = 1;
for my $i (0..3) {
for my $j (0..2) {
for my $k (0..1) {
	my @t = qw/A B C D/;
	printf "graph g%02d\n", $iter++;
	printf "  node input input A 32 1 B 32 1 C 32 1 D 32 1\n";
	printf "  node macc  macc  A 32 1 B 32 1 C 32 1 D 32 1\n";
	printf "  connect input A macc %s\n", splice(@t,$i,1);
	printf "  connect input B macc %s\n", splice(@t,$j,1);
	printf "  connect input C macc %s\n", splice(@t,$k,1);
	printf "  connect input D macc %s\n", splice(@t,0,1);
	printf "endgraph\n";
	printf "\n";
}}}

$iter = 1;
printf "graph gXL\n";
for my $i (0..3) {
for my $j (0..2) {
for my $k (0..1) {
	my $id = sprintf "_%02d", $iter++;
	my @t = qw/A B C D/;
	printf "  node input$id input A 16 B 16 C 16 D 16\n";
	printf "  node macc$id  macc  A 16 B 16 C 16 D 16\n";
	printf "  connect input$id A macc$id %s\n", splice(@t,$i,1);
	printf "  connect input$id B macc$id %s\n", splice(@t,$j,1);
	printf "  connect input$id C macc$id %s\n", splice(@t,$k,1);
	printf "  connect input$id D macc$id %s\n", splice(@t,0,1);
}}}
printf "endgraph\n";
printf "\n";


printf "swapgroup macc A B\n";
printf "swapgroup macc C D\n";
printf "swapperm macc A B C D : C D A B\n";

for my $i (@matches) {
for my $j (@non_matches) {
	printf "solve %s %s\n", $i, $j;
}}
printf "expect 0\n\n";

for my $i (@matches) {
for my $j (@matches) {
	printf "solve %s %s\n", $i, $j;
}}
printf "expect %d\n\n", @matches*@matches;

printf "solve g01 gXL false\n";
printf "expect 8\n";

printf "solve g03 gXL false\n";
printf "expect 8\n";

printf "solve g04 gXL false\n";
printf "expect 8\n";

