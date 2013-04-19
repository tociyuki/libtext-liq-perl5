#!/usr/bin/perl
use strict;
use warnings;
use Carp;
use English qw(-no_match_vars);

# genliq.pl - the parsing table generator for Text-Liq grammar.

my $EMPTY = "~empty";
my $ENDMARK = "EOF";
my $SP = qr{[ \t]*(?:(?:\#[^\n]*)?\n[ \t]*)*}msx;
my $DERIVS = 0;
my $PARSED = 1;

my $BNF = <<'EOS';
#token PLAIN CONST STRING NUMBER ESCAPE NOESCAPE
#token ASSIGN CAPTURE DECREMENT INCREMENT INCLUDE CASE
#token FOR IF UNLESS ELSE IFCHANGED CYCLE FILTER
#token OR AND NOT RANGE REVERSED BREAK CONTINUE
#token WITH EQUIV IN DOT COLON COMMA IDENT CMP R RR RRR ELSIF WHEN
#token ENDIF ENDUNLESS ENDFOR ENDCASE ENDCAPTURE ENDIFCHANGED
#token LPAREN RPAREN LSQUARE RSQUARE

block
    : PLAIN {append} block
    | ESCAPE   value {make_escape} pipeline RR  {append_first} block
    | NOESCAPE value {make_escape} pipeline RRR {append_first} block
    | ASSIGN variable EQUIV value {make_assign}
      pipeline R {append_first} block
    | IF {make_if} expression R {append_first} block
      elsif_clauses if_else_clause ENDIF {end_node} block
    | UNLESS {make_if} expression {flip_unless} R {append_first} block
      elsif_clauses if_else_clause ENDUNLESS {end_node} block
    | CASE value R {make_case} plains
      when_clause when_clauses case_else_clause
      ENDCASE {end_node} block
    | FOR variable IN {srcmark} for_list {srcyank} {make_for}
      for_slice R {append_for_slice} block for_else_clause
      ENDFOR {end_node} block
    | CAPTURE variable {make_capture} pipeline R {append_first} block
      ENDCAPTURE {end_node} block
    | CYCLE {append} block
    | DECREMENT variable R {append_increment} block
    | INCREMENT variable R {append_increment} block
    | IFCHANGED {make_ifchanged} block
      ENDIFCHANGED {end_ifchanged} block
    | INCLUDE value {make_include}
      include_with include_arguments R {append_first} block
    | BREAK {append_break} block
    | CONTINUE {append_break} block
    | # empty

elsif_clauses
    : ELSIF {make_elsif} expression R {append_first} block elsif_clauses
    | # empty

plains
    : PLAIN {append} plains
    | # empty

when_clauses
    : when_clause when_clauses
    | # empty

when_clause
    : WHEN value {make_when} when_values R {append_first} block

if_else_clause
    : else_clause
    | # empty

case_else_clause
    : else_clause
    | # empty

for_else_clause
    : else_clause
    | # empty

else_clause
    : ELSE {make_else} block

pipeline
    : FILTER IDENT {make_filter} filter_arguments {append} pipeline
    | # empty

filter_arguments
    : COLON value {append_second} filter_comma_arguments
    | # empty

filter_comma_arguments
    : COMMA value {append_second} filter_comma_arguments
    | # empty

for_list
    : LPAREN value RANGE value RPAREN {for_list_range}
    | value

for_slice
    : IDENT COLON for_offset for_slice
    | REVERSED {set_for_reversed} for_slice
    | # empty

for_offset
    : CONTINUE {set_offset_continue}
    | value {set_offset_value}

when_values
    : OR    value {append_second} when_values
    | COMMA value {append_second} when_values
    | # empty

include_with
    : WITH variable {include_with}
    | FOR  variable {include_with}
    | # empty

include_arguments
    : variable COLON value {append_include_arguments} include_comma
      include_arguments
    | # empty

include_comma
    : COMMA {ignore}
    | # empty

expression
    : expression3 expression2 expression1

expression1
    : OR expression3 expression2 {make_binary} expression1
    | # empty

expression2
    : AND expression3 {make_binary} expression2
    | # empty

expression3
    : LPAREN expression RPAREN {make_subexpression}
    | NOT value {make_unary} expression4
    | value expression4

expression4
    : CMP value {make_binary}
    | # empty

value
    : CONST | variable | STRING | NUMBER

variable
    : IDENT {make_variable} selectors

selectors
    : DOT IDENT {append_second} selectors
    | LSQUARE value RSQUARE {append_second3} selectors
    | # empty
EOS

exit main($BNF);

sub main {
    my($source) = @_;
    my $grammar = parse($source);
    my $tokens = make_token_list($source, $grammar);
    my $first = make_first_set($grammar);
    my $follow = make_follow_set($grammar, $first);
    my $table = make_parsing_table($grammar, $first, $follow);
    my($nonterminals, $base, $check)
        = make_double_array($grammar, $tokens, $table);
    my $list = <<'EOS';
# --- BEGIN generated by `perl genliq.pl`
EOS
    $list .= list_nonterminals($nonterminals);
    $list .= list_double_array($base, $check);
    $list .= list_parsing_table($grammar, $table);
    $list .= <<'EOS';
# --- END generated
EOS
    print $list;
    return 0;
}

# $base->[$base->[$nonterminal->{$s}] + $tokens->{$a}] == $rule->{$s}{$a}
# $check->[$base->[$nonterminal->{$s}] + $tokens->{$a}] == $nonterminal->{$s}
sub make_double_array {
    my($grammar, $tokens, $table) = @_;
    my @base = (-1, 0);
    my @check = (-1, 0);
    my $parent = 1 + keys %{$tokens};
    $base[$parent] = 0;
    $check[$parent] = 0;
    my %nonterminal;
    for my $lhs (map { $_->[0] } @{$grammar}) {
        next if $nonterminal{$lhs};
        $nonterminal{$lhs} = $parent;
        my $row = $table->{$lhs};
        my @edge = sort { $a <=> $b } map { $tokens->{$_} } keys %{$row};
        my $b = 1 - $edge[0];
        while (_any(sub{ defined $check[$b + $_] }, @edge)) {
            ++$b
        }
        $base[$parent] = $b;
        for my $j (@edge) {
            $check[$b + $j] = $parent;
        }
        while (defined $check[++$parent]) {
            # do nothing
        }
        $base[$parent] = 0;
        $check[$parent] = 0;
    }
    return (\%nonterminal, \@base, \@check);
}

sub parse {
    my($bnf) = @_;
    my $v = _parse_grammar([\$bnf, 0]) or croak "SyntaxError: grammar error.";
    (length $bnf) == $v->[$DERIVS][1] or croak "SyntaxError: grammar error.";
    return $v->[$PARSED];
}

sub make_token_list {
    my($source, $grammar) = @_;
    my %h = ('EOF' => 1);
    my $i = 2;
    while ($source =~ m/^\#token[ ]+([^\n\#]+)/gmsx) {
        for my $token (split /[ ]+/msx, $1) {
            next if $token eq 'EOF';
            if (! exists $h{$token}) {
                $h{$token} = $i++;
            }
            else {
                carp "#token $token is redefined.\n";
            }
        }
    }
    my %nonterminal;
    for my $product (@{$grammar}) {
        my $lhs = $product->[0];
        $nonterminal{$lhs} ||= $lhs;
    }
    for my $term (map { @{$_->[1]} } @{$grammar}) {
        next if $term !~ m/\A[^\W0-9]\w*\z/msx;
        next if exists $nonterminal{$term} || exists $h{$term};
        $h{$term} = $i++;
    }
    return \%h;
}

sub make_first_set {
    my($grammar) = @_;
    $grammar = _reject_grammar_actions($grammar);
    my %nonterminal = map { $_->[0] => $_->[0] } @{$grammar};
    my $first = {};
    my $changed = 0;
    my $update = sub{ $changed = 1 };
    while (1) {
        $changed = 0;
        for my $product (@{$grammar}) {
            my($lhs, $rhs) = @{$product};
            _percolate($first, $lhs, {}, $update);
            my $rhs_empty = 1;
            for my $x (@{$rhs}) {
                if (exists $nonterminal{$x}) {
                    _percolate($first, $x, {}, $update);
                    for my $a (keys %{$first->{$x}}) {
                        next if $a eq $EMPTY;
                        _percolate($first->{$lhs}, $a, $a, $update);
                    }
                    if (! exists $first->{$x}{$EMPTY}) {
                        $rhs_empty = 0;
                        last;
                    }
                }
                else {
                    _percolate($first->{$lhs}, $x, $x, $update);
                    $rhs_empty = 0;
                    last;
                }
            }
            if ($rhs_empty) {
                _percolate($first->{$lhs}, $EMPTY, $EMPTY, $update);
            }
        }
        last if ! $changed;
    }
    return $first;
}

sub _collect_first {
    my($sequence, $first) = @_;
    my %set;
    for my $a (@{$sequence}) {
        if (! exists $first->{$a}) { # is terminal
            $set{$a} = $a;
            last;
        }
        for my $x (keys %{$first->{$a}}) {
            next if $x eq $EMPTY;
            $set{$x} = $x;
        }
        last if ! exists $first->{$a}{$EMPTY};
    }
    return keys %set;
}

sub make_follow_set {
    my($grammar, $first) = @_;
    $grammar = _reject_grammar_actions($grammar);
    my %nonterminal = map { $_->[0] => $_->[0] } @{$grammar};
    my $follow = {};
    $follow->{$grammar->[0][0]}{$ENDMARK} = $ENDMARK;
    my $changed = 0;
    my $update = sub{ $changed = 1 };
    while (1) {
        $changed = 0;
        for my $product (@{$grammar}) {
            my($lhs, $rhs) = @{$product};
            _percolate($follow, $lhs, {}, $update);
            for my $i (0 .. $#{$rhs} - 1) {
                my($b, $beta) = @{$rhs}[$i, $i + 1];
                next if ! exists $nonterminal{$b};
                _percolate($follow, $b, {}, $update);
                if (! exists $nonterminal{$beta}) {
                    _percolate($follow->{$b}, $beta, $beta, $update);
                }
                else {
                    for my $x (keys %{$first->{$beta}}) {
                        next if $x eq $EMPTY;
                        _percolate($follow->{$b}, $x, $x, $update);
                    }
                    if (exists $first->{$beta}{$EMPTY}) {
                        for my $x (keys %{$follow->{$beta}}) {
                            _percolate($follow->{$b}, $x, $x, $update);
                        }
                    }
                }
            }
            for my $b (reverse @{$rhs}) {
                last if ! exists $nonterminal{$b};
                for my $x (keys %{$follow->{$lhs}}) {
                    _percolate($follow, $b, {}, $update);
                    _percolate($follow->{$b}, $x, $x, $update);
                }
                last if ! exists $first->{$b}{$EMPTY};
            }
        }
        last if ! $changed;
    }
    return $follow;
}

sub make_parsing_table {
    my($grammar, $first, $follow) = @_;
    my $table = {};
    for my $product (@{$grammar}) {
        my($lhs, $rhs) = @{$product};
        for my $w (_collect_first($rhs, $first)) {
            if (exists $table->{$lhs}{$w}) {
                croak "Conflict: FIRST/FIRST $lhs : $w.\n";
            }
            $table->{$lhs}{$w} = $rhs;
        }
    }
    for my $lhs (keys %{$table}) {
        next if ! exists $first->{$lhs}{$EMPTY};
        for my $w (keys %{$follow->{$lhs}}) {
            if (exists $table->{$lhs}{$w}) {
                croak "Conflict: FIRST/FOLLOW $lhs : $w.\n";
            }
            $table->{$lhs}{$w} = [];
        }
    }
    return $table;
}

sub list_terminals {
    my($terminals) = @_;
    my @a;
    for my $w (keys %{$terminals}) {
        $a[$terminals->{$w} - 1] = "\x24" . $w;
    }
    my $t = 'my( # terminals' . _fold_list(q(), @a) . ",\n";
    $t .= ') = (1 .. ' .  (0 + @a) . ");\n";
    $t .= "\n";
    return $t;
}

sub list_nonterminals {
    my($nonterminals) = @_;
    my @a;
    my @b;
    for my $w (
        sort { $nonterminals->{$a} <=> $nonterminals->{$b} }
        keys %{$nonterminals}
    ) {
        push @a, "\x24" . $w;
        push @b, $nonterminals->{$w};
    }
    my $t = <<'EOS';
# nonterminals : index of Double Array @rule and @rule_check
#   $rule[$rule[$symbol] + $next_token] = \@symbols
#   $rule_check[$rule[$symbol] + $next_token] == $symbol
EOS
    $t .= 'my(' . _fold_list(q(), @a) . ",\n";
    $t .= ") = (" . _fold_list(q(), @b) . ",\n);\n";
    $t .= <<"EOS";
my \x{24}LAST_NONTERMINAL = $a[-1];
my \x{24}srcmark = 500;
my \x{24}srcyank = 501;
EOS
    return $t;
}

sub list_double_array {
    my($base, $check) = @_;
    my $t = 'my @rule = (';
    $t .= _fold_list(q(), map { defined $_ ? $_ : -1 } @{$base});
    $t .= ",\n);\n";
    $t .= 'my @rule_check = (';
    $t .= _fold_list(q(), map { defined $_ ? $_ : -1 } @{$check});
    $t .= ",\n);\n";
    return $t;    
}

sub list_parsing_table {
    my($grammar, $table) = @_;
    my $t = q();
    my $prevlhs = q();
    for my $product (@{$grammar}) {
        my($lhs, $rhs) = @{$product};
        if ($lhs ne $prevlhs) {
            $t .= "\n";
        }
        $prevlhs = $lhs;
        my $row = $table->{$lhs};
        my @k = sort grep {
            "$row->{$_}" eq "$rhs" || (! @{$row->{$_}} && ! @{$rhs})
        } keys %{$row};
        my @a = map {
              $_ eq '{srcmark}' ? "\x24" . 'srcmark'
            : $_ eq '{srcyank}' ? "\x24" . 'srcyank'
            : m/\{(.*?)\}/msx ? q(\\&_) . $1 : "\x24" . $_
        } @{$row->{$k[0]}};

        if (@k > 1) {
            my @b = map { "\x24" . $_ } @k;
            my $s0 = join q(, ), @b;
            my $s1 = (length $s0) < 76 - 14 ? $s0 : _fold_list(q(), @b) . ",\n";
            $t .= "for my \x{24}i (" . $s1;
            $t .= q[) {] . "\n";
            my $s2 = q(    $rule[$rule[$) . $lhs . q(]+$i] = [);
            my $s3 = join q(, ), @a;
            my $s4 = (length $s2 . $s3) < 76 - 2 ? $s3 : _fold_list(q[    ], @a); 
            $t .= $s2 . $s4 . "];\n";
            $t .= q[}] . "\n";
        }
        else {
            my $s0 = q($rule[$rule[$) . $lhs . q(]+$) . $k[0] . q(] = [);
            my $s1 = join q(, ), @a;
            my $s2 = (length $s0 . $s1) < 76 - 2 ? $s1 : _fold_list(q(), @a); 
            $t .= $s0 . $s2 . "];\n";
        }
    }
    return $t;
}

# grammar -> SP (symbol ':' SP expression)*
# symbol -> [^\W0-9_][\w]* SP
sub _parse_grammar {
    my($derivs0) = @_;
    my @products;
    $derivs0 = (_scan($derivs0, $SP) || [$derivs0])->[$DERIVS];
    while (1) {
        my $v1 = _scan($derivs0, qr/([^\W0-9_]\w*)$SP[:]$SP/msx) or last;
        my $v2 = _parse_expression($v1->[$DERIVS]) or return;
        my $v3 = _scan($v2->[$DERIVS], qr/[;]$SP/msx) || $v2;
        push @products,
            map { [$v1->[$PARSED], $_] } @{$v2->[$PARSED]};
        $derivs0 = $v3->[$DERIVS];
    }
    return [$derivs0, \@products];
}

# expression -> sequence ('|' [\s]* sequence)*
sub _parse_expression {
    my($derivs0) = @_;
    my @sequences;
    my $v1 = _parse_sequence($derivs0) or return;
    push @sequences, $v1->[$PARSED];
    my $derivs1 = $v1->[$DERIVS];
    while (1) {
        my $v2 = _scan($derivs1, qr/[|]$SP/msx) or last;
        my $v3 = _parse_sequence($v2->[$DERIVS]) or return;
        push @sequences, $v3->[$PARSED];
        $derivs1 = $v3->[$DERIVS];
    }
    return [$derivs1, \@sequences];
}

# sequence -> (!(symbol ':') symbol / action)*
# action -> '{' [\s]* [^\W0-9][\w]* [\s]* '}' [\s]*
sub _parse_sequence {
    my($derivs0) = @_;
    my @terms;
    while (not _scan($derivs0, qr/([;])|([^\W0-9_]\w*)$SP[:]/msx)) {
        my $v1 = _scan($derivs0, qr/([^\W0-9_]\w*)$SP/msx);
        if ($v1) {
            push @terms, $v1->[$PARSED];
            $derivs0 = $v1->[$DERIVS];
            next;
        }
        my $v2 = _scan($derivs0, qr/\{$SP([^\W0-9]\w*)$SP\}$SP/msx);
        if ($v2) {
            push @terms, q({) . $v2->[$PARSED] . q(});
            $derivs0 = $v2->[$DERIVS];
            next;
        }
        last;
    }
    return [$derivs0, \@terms];
}

sub _scan {
    my($derivs, $pattern) = @_;
    my($ref, $pos) = @{$derivs};
    pos(${$ref}) = $pos;
    if (${$ref} =~ m/\G$pattern/gcmsx) {
        return [[$ref, pos(${$ref})], $LAST_PAREN_MATCH];
    }
    return;
}

sub _any {
    my($yield, @a) = @_;
    for (@a) {
        return 1 if $yield->($_);
    }
    return;
}

sub _reject_grammar_actions {
    my($grammar) = @_;
    my @result;
    for my $product (@{$grammar}) {
        my($lhs, $rhs) = @{$product};
        push @result, [$lhs, [grep { m/\A[^\{]/ } @{$rhs}]];
    }
    return \@result;
}

sub _percolate {
    my($hash, $key, $value, $yield) = @_;
    if (! exists $hash->{$key}) {
        $hash->{$key} = $value;
        $yield->();
    }
    return;
}

sub _fold_list {
    my($indent, @a) = @_;
    my $t = "\n" . $indent . q(    );
    my $c = length $t;
    for my $i (0 .. $#a) {
        my $w = $a[$i];
        if ((length $w) + $c + 2 > 76) {
            $t .= "\n" . $indent . q(    ) . $w;
            $c = (length $indent . $w) + 6;
        }
        else {
            $t .= $w;
            $c += (length $w) + 2;
        }
        last if $i == $#a;
        $t .= q(, );
    }
    return $t;
}

__END__

=pod

=head1 NAME

genliq.pl - parsing table generator for Text-Liq grammar

=head1 VERSION

0.01

=head1 SYNOPSIS

    $ perl genliq.pl

=head1 DESCRIPTION

This script provides Text-Liq/lib/Text/Liq.pm to generate
the parsing table from the Liquid markups Grammar.

=head1 SEE ALSO

L<Text::Liq>

=head1 AUTHOR

MIZUTANI Tociyuki  C<< <tociyuki at gmail.com> >>

=head1 LICENSE AND COPYRIGHT

Copyright (c) 2013, MIZUTANI Tociyuki.  All rights reserved.

This module is free software; you can redistribute it and/or
modify it under the same terms as Perl itself. See L<perlartistic>.

=head1 DISCLAIMER OF WARRANTY

BECAUSE THIS SOFTWARE IS LICENSED FREE OF CHARGE, THERE IS NO WARRANTY
FOR THE SOFTWARE, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN
OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES
PROVIDE THE SOFTWARE "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER
EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE
ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE SOFTWARE IS WITH
YOU. SHOULD THE SOFTWARE PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL
NECESSARY SERVICING, REPAIR, OR CORRECTION.

IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MAY MODIFY AND/OR
REDISTRIBUTE THE SOFTWARE AS PERMITTED BY THE ABOVE LICENCE, BE
LIABLE TO YOU FOR DAMAGES, INCLUDING ANY GENERAL, SPECIAL, INCIDENTAL,
OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OR INABILITY TO USE
THE SOFTWARE (INCLUDING BUT NOT LIMITED TO LOSS OF DATA OR DATA BEING
RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD PARTIES OR A
FAILURE OF THE SOFTWARE TO OPERATE WITH ANY OTHER SOFTWARE), EVEN IF
SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.

=cut

