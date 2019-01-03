#! /usr/bin/env perl


use strict;
use warnings;

use warnings FATAL => 'uninitialized';
use Data::Dumper;


use Carp 'verbose';
use Carp qw[croak];


# print dumper if debug
sub edumper {
  my (@args) = @_;
  print Dumper(\@args) if $ENV{DEBUG};
}


# not named pop_comma because that suggests that
# pop_comma(@a) works like pop.
# given the choice between a strange name and using prototypes
# I pick strange name.
sub pop_comma_arr_ref {
  my ($arr_ref) = @_;
  croak unless defined $arr_ref;
  return 0 unless @$arr_ref;
  if ($arr_ref->[-1] eq ',') {
    pop @$arr_ref;
    return 1;
  } else {
    return 0;
  }
}


my $k_identifier = 1;


my $lowercase_c_identifier_pat = qr/^[_a-z][_a-zA-Z0-9]*$/;

sub lowercase_c_identifier {
  my ($str) = @_;
  if ($str =~ $lowercase_c_identifier_pat) {
    return 1;
  } else {
    return 0;
  }
}


sub pop2_arr_ref {
  my ($arr_ref) = @_;
  croak unless wantarray;
  my @out = ($arr_ref->[-2], $arr_ref->[-1]);
  $#$arr_ref -= 2;
  return @out;
}


sub translate_rpn {
  my ($str) = @_;
  edumper({rpn => $str});
  my @components;
  my @vars;
  $str =~ s/^\s+//;
  $str =~ s/\s+$//;
  my @tokens = split /\s+/, $str;
  my @stack;
  # run along the tokens, push things onto the stack
  # if an operator is at the top of the stack, combine
  # things on the stack according to the arity of the
  # operator
  # NOTE: this technique will stop working once we add
  # things to the language like "dup"
  for my $word (@tokens) {
    if (lowercase_c_identifier($word)) {
      push @stack, "pvar_$word";
      push @vars, "pvar_$word";
    }
    elsif ($word eq '*') {
      @stack >= 2 or croak 'virtual stack underflow';
      push @stack, ('and' . '(' . (join ",", pop2_arr_ref(\@stack)) . ')');
    }
    elsif ($word eq '+') {
      @stack >= 2 or croak 'virtual stack underflow';
      push @stack, ('or' . '(' . (join ",", pop2_arr_ref(\@stack)) . ')');
    }
    elsif ($word eq '!') {
      @stack >= 1 or croak 'virtual stack underflow';
      push @stack, ('not' . '(' . pop(@stack) . ')');
    }
    elsif ($word eq '/') {
      @stack >= 2 or croak 'stack underflow';
      push @stack, ('if' . '(' . (join ",", pop2_arr_ref(\@stack)) . ')');
    }
    else {
      croak "---$word---";
    }
  }
  croak unless @stack == 1;
  my ($expr) = @stack;
  my $vars = {};
  $vars->{$_} = 1 foreach @vars;
  my $out = {
    vars => $vars,
    expr => $expr,
  };
  edumper($out);
  return $out;
}


my $script_template = do {
  local $/;
  scalar <DATA>;
};


my $invoke_proof = q[swipl -s /tmp/proof.P -g 'the_proof(X), classify_proof(X, Z), print(Z).' -t 'halt'];


my ($proof_script) = @ARGV;

open my $fh, '<', $proof_script or croak 'cannot open file!';

unlink("/tmp/proof.P");
open my $sink, '>', "/tmp/proof.P" or croak;


my @prologified_proof_lines;
my %vars;
while (<$fh>) {
  chomp;
  my $line = $_;
  my $translated = translate_rpn($line);
  push @prologified_proof_lines, $translated->{expr};
  %vars = (%vars, %{ $translated->{vars} });
}


my $prolog_proof_expr = join ",\n", @prologified_proof_lines;

my @vars = map +("pvar($_)."), keys(%vars);

my $vars_expr = join "\n", @vars;


my (%replacements) = (
  '%%%THE_VARIABLES%%%' => $vars_expr,
  '%%%THE_PROOF%%%'     => $prolog_proof_expr,
);

$script_template =~ s/(%%%THE_VARIABLES%%%|%%%THE_PROOF%%%)/$replacements{$1}/ge;

print {$sink} $script_template;

exec($invoke_proof);


__DATA__
% style guide for template
% metavariables to be replaced in the template ( %%SOME_METAVARIABLE%% )
% but with three '%'s not two
%
% the simplest possible realization (with only if and not)
% is basically unusable

% SWIPL silence errors
:- style_check(-discontiguous).
:- style_check(-singleton).


% well-formedness
% defines what it means to be a single formula of a
% proof term
expr(false).
expr(EXPR) :- pvar(EXPR).
expr(if(E1, E2)) :- expr(E1), expr(E2).
expr(and(E1, E2)) :- expr(E1), expr(E2).
expr(or(E1, E2)) :- expr(E1), expr(E2).
expr(not(EXPR)) :- expr(EXPR).
expr(if(E1, E2)) :- expr(E1), expr(E2).



% entailment related rules have
% the out parameter LAST

% because of the search procedure the order
% of in-arguments to an entailed_* procedure
% does not matter.


% or-related rules
% P |- P + Q
entailed_or(P, or(P, Q)).
% P |- Q + P
entailed_or(P, or(Q, P)).
% P + Q, not(Q) |- P
bentailed_or(or(P, Q), not(P), Q).
% not(Q), P + Q |- P
bentailed_or(or(P, Q), not(Q), P).


% and-related rules
bentailed_and(P, Q, and(P, Q)).
bentailed_and(P, Q, and(Q, P)).
entailed_and(and(P, Q), P).
entailed_and(and(P, Q), Q).
bentailed_and(and(P, Q), not(P), not(Q)).
bentailed_and(and(P, Q), not(Q), not(P)).


% negation-related rules
% double negation elimination
entailed_neg(not(not(P)), P).
% double negation introduction
entailed_neg(P, not(not(P))).


% entailed_if is not primitive
% introducing new premise
entailed_if(Q, if(P, Q)).
% modus ponens
bentailed_if(P, if(P, Q), Q).
% denying the consequent
entailed_if(not(Q), if(P, Q)).
% getting into or land from if
entailed_if(if(P,Q), or(not(P), Q)).


% noncontra and efq
entailed_false(false, P).
bentailed_false(P, not(P), false).



entailed(C, _) :- axiom(C).

% unary inference rules
entailed(C, PREMS) :- member(X, PREMS),  entailed_or(X, C).
entailed(C, PREMS) :- member(X, PREMS), entailed_and(X, C).
entailed(C, PREMS) :- member(X, PREMS),  entailed_if(X, C).
entailed(C, PREMS) :- member(X, PREMS), entailed_not(X, C).

% binary inference rules
entailed(C, PREMS) :- member(X, PREMS), member(Y, PREMS),  bentailed_or(X, C).
entailed(C, PREMS) :- member(X, PREMS), member(Y, PREMS), bentailed_and(X, C).
entailed(C, PREMS) :- member(X, PREMS), member(Y, PREMS),  bentailed_if(X, C).
entailed(C, PREMS) :- member(X, PREMS), member(Y, PREMS), bentailed_not(X, C).


% axioms for hilbert system
% since we can also convert if to or we might not
% need anything else

axiom(if(F, F)).

axiom(if(F, if(P, F))).

axiom(if(
  if(F, if(P, X)),
  if(if(F, P), if(P, X)))).

axiom(if(if(not(F), not(P)),
        if(P, F))).

% variable section

%%%THE_VARIABLES%%%

% determine whether to accept a proof
% https://stackoverflow.com/a/50026860/931154
prefix_of([], _).
prefix_of([H|NT], [H|T]) :- prefix_of(NT, T).

valid_proof_fragment([]).
valid_proof_fragment(PREFIX) :-
  reverse(PREFIX, [CONCLUSION|PREMISES]),
  entailed(CONCLUSION, PREMISES).

reject_proof(ITEMS, BADITEM) :- prefix_of(BADITEM, ITEMS), \+ valid_proof_fragment(BADITEM).


malformed_list(X, W) :- member(W, X), \+ expr(W).

malformed_list(X) :- malformed_list(X, _).

wellformed_list(X) :- \+ malformed_list(X).


classify_proof(ITEMS, OUT) :-
  (malformed_list(ITEMS, W), OUT = malformed(W)) ;
  (reject_proof(ITEMS, BADITEM), OUT = bad(BADITEM)) ;
  (OUT = good) .

% target
the_proof(
  [
    %%%THE_PROOF%%%
  ]
).
