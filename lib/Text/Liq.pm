package Text::Liq;
use warnings;
use strict;
use Carp;
use English qw(-no_match_vars);
use Scalar::Util qw(looks_like_number);
use integer;

our $VERSION = '0.01';

## no critic qw(EnumeratedClasses EscapedMetacharacters)

my $STACK_LIMIT = 50;

my(# 50 terminals
    $EOF, $PLAIN, $CONST, $STRING, $NUMBER, $ESCAPE, $NOESCAPE,
    $ASSIGN, $CAPTURE, $DECREMENT, $INCREMENT, $INCLUDE, $CASE,
    $FOR, $IF, $UNLESS, $ELSE, $IFCHANGED, $CYCLE, $FILTER,
    $OR, $AND, $NOT, $RANGE, $REVERSED, $BREAK, $CONTINUE,
    $WITH, $EQUIV, $IN, $DOT, $COLON, $COMMA,
    $IDENT, $CMP, $R, $RR, $RRR, $ELSIF, $WHEN, 
    $ENDIF, $ENDUNLESS, $ENDFOR, $ENDCASE, $ENDCAPTURE, $ENDIFCHANGED,
    $LPAREN, $RPAREN, $LSQUARE, $RSQUARE,
) = (0 .. 49);
my $LAST_TERMINAL = $RSQUARE;
# template symbol $EOF .. $CONTINUE, $EQ .. $BEGIN
my(
    $EQ, $NE, $LT, $LE, $GT, $GE, $CONTAINS, $VARIABLE, $BEGIN,
) = ($WITH .. $WITH+8);
my $NONTERM = -100;
my(# 23 nonterminals
    $block, $elsif_clauses, $else_clause, $plains, $when_clauses,
    $pipeline, $filter_arguments, $filter_comma_arguments,
    $for_list, $for_slice, $for_offset, $when_values,
    $include_with, $include_arguments, $include_comma,
    $value, $variable, $selectors, $expression, $expression1,
    $expression2, $expression3, $expression4,
) = (0-$NONTERM .. 22-$NONTERM);
my $LAST_NONTERMINAL = $expression4;
my %LCONST = (
    'nil' => undef, 'null' => undef, 'NULL' => undef,
    'empty' => [], 'true' => 1, 'false' => q(),
);
my %KEYWORD = (
    'assign' => $ASSIGN, 'capture' => $CAPTURE, 'decrement' => $DECREMENT,
    'increment' => $INCREMENT, 'include' => $INCLUDE, 'case' => $CASE,
    'for' => $FOR, 'if' => $IF, 'unless' => $UNLESS, 'elsif' => $ELSIF,
    'when' => $WHEN, 'endif' => $ENDIF, 'endunless' => $ENDUNLESS,
    'break' => $BREAK, 'continue' => $CONTINUE,
    'endfor' => $ENDFOR, 'endcase' => $ENDCASE, 'endcapture' => $ENDCAPTURE,
    'else' => $ELSE, 'ifchanged' => $IFCHANGED, 'endifchanged' => $ENDIFCHANGED,
    q[==] => $CMP, q[!=] => $CMP, q[<] => $CMP, q[<=] => $CMP,
    q[>] => $CMP, q[>=] => $CMP, 'contains' => $CMP,
    q[{{] => $ESCAPE, q[}}] => $RR, q[{{{] => $NOESCAPE, q[}}}] => $RRR,
    q[%}] => $R, 'in' => $IN,
    'reversed' => $REVERSED, 'or' => $OR, 'and' => $AND, 'not' => $NOT,
    q[||] => $OR, q[&&] => $AND, q[!] => $NOT, 'with' => $WITH,
    q[=] => $EQUIV, q[|] => $FILTER, q[:] => $COLON, q[,] => $COMMA,
    q[(] => $LPAREN, q[)] => $RPAREN, q[.] => $DOT, q[..] => $RANGE,
    q([) => $LSQUARE, q(]) => $RSQUARE,
);
my %COMPARE = (
    q[==] => $EQ, q[!=] => $NE, q[<] => $LT, q[<=] => $LE,
    q[>] => $GT, q[>=] => $GE, 'contains' => $CONTAINS,
);
my $LNUM = qr/([+-]?[0-9]+(?:[.][0-9]+)?(?:[eE][+-]?[0-9]+)?)/msx;
my $LSTR = qr/'([^']*)'|"([^"]*)"/msx;
my $LPUNCT = qr/([:,()\[\]]|==?|!=?|<[=>]?|>=?|\|\|?|&&|[.][.]?)/msx;
my $LWORD = qr/([^\W0-9_]\w*[?]?)/msx;
my $LTAG = 'assign|ca(?:pture|se)|decrement|elsif|for'
           . '|i(?:f|nc(?:rement|lude))|unless|when';
my $LTAG1 = 'break|continue|else|ifchanged'
           . '|end(?:ca(?:se|pture)|for|if(?:changed)?|unless)';
my $LRAW = qr/raw\s*%\}\n?(.*?)\{%\s*endraw\s*%\}\n?/msx;
my $LCOMMENT = qr/comment\s*%\}\n?(.*?)\{%\s*endcomment\s*%\}\n?/msx;
my $LMARKUP = qr/($LTAG)\s+|($LTAG1)\s*%\}\n?|(cycle)\s+|$LRAW|$LCOMMENT/msx;
my $LMARKIN = qr/$LPUNCT|$LWORD|$LNUM|$LSTR/msx;

my @rule;
for my $i (0 .. $NONTERM+$LAST_NONTERMINAL) {
    $rule[$i] = [];
    $#{$rule[$i]} = $LAST_TERMINAL;
}
$rule[$NONTERM+$block][$PLAIN] = [
    $PLAIN, \&_append, $block];
$rule[$NONTERM+$block][$ESCAPE] = [
    $ESCAPE, $value, \&_make_escape, $pipeline, $RR, \&_append_first, $block];
$rule[$NONTERM+$block][$NOESCAPE] = [
    $NOESCAPE, $value, \&_make_escape, $pipeline, $RRR,
    \&_append_first, $block];
$rule[$NONTERM+$block][$ASSIGN] = [
    $ASSIGN, $variable, $EQUIV, $value, \&_make_assign, $pipeline, $R,
    \&_append_first, $block];
$rule[$NONTERM+$block][$IF] = [
    $IF, \&_begin_node, $expression, $R, \&_append_first,
    $block, $elsif_clauses, $else_clause,
    $ENDIF, \&_end_node, $block];
$rule[$NONTERM+$block][$UNLESS] = [
    $UNLESS, \&_begin_node, $expression, \&_make_unless, $R, \&_append_first,
    $block, $elsif_clauses, $else_clause,
    $ENDUNLESS, \&_end_node, $block];
$rule[$NONTERM+$block][$FOR] = [
    $FOR, $variable, $IN, $for_list, \&_make_for,
    $for_slice, $R, \&_append_for_slice, $block, $else_clause,
    $ENDFOR, \&_end_node, $block];
$rule[$NONTERM+$block][$CASE] = [
    $CASE, $value, $R, \&_make_case, $plains,
    $when_clauses, $else_clause,
    $ENDCASE, \&_end_node, $block];
$rule[$NONTERM+$block][$CAPTURE] = [
    $CAPTURE, $variable, \&_make_capture, $pipeline, $R, \&_append_first,
    $block, $ENDCAPTURE, \&_end_node, $block];
$rule[$NONTERM+$block][$CYCLE] = [$CYCLE, \&_append, $block];
$rule[$NONTERM+$block][$DECREMENT] = [
    $DECREMENT, $variable, $R, \&_append_increment, $block];
$rule[$NONTERM+$block][$INCREMENT] = [
    $INCREMENT, $variable, $R, \&_append_increment, $block];
$rule[$NONTERM+$block][$IFCHANGED] = [
    $IFCHANGED, \&_make_ifchanged, $block,
    $ENDIFCHANGED, \&_end_ifchanged, $block];
$rule[$NONTERM+$block][$INCLUDE] = [
    $INCLUDE, $value, \&_make_include,
    $include_with, $include_arguments, $R, \&_append_first, $block];
$rule[$NONTERM+$block][$BREAK] = [
    $BREAK, \&_append_break, $block];
$rule[$NONTERM+$block][$CONTINUE] = [
    $CONTINUE, \&_append_break, $block];
for my $i (
    $EOF, $ELSIF, $ELSE, $ENDIF, $ENDUNLESS, $ENDCAPTURE,
    $ENDIFCHANGED, $ENDFOR, $ENDCASE, $WHEN,
) {
    $rule[$NONTERM+$block][$i] = [];
}

$rule[$NONTERM+$elsif_clauses][$ELSIF] = [
    $ELSIF, \&_make_elsif, $expression, $R, \&_append_first,
    $block, $elsif_clauses];
for my $i ($ELSE, $ENDIF, $ENDUNLESS) {
    $rule[$NONTERM+$elsif_clauses][$i] = [];
}

$rule[$NONTERM+$plains][$PLAIN] = [
    $PLAIN, \&_append, $plains];
for my $i ($WHEN, $ELSE, $ENDCASE) {
    $rule[$NONTERM+$plains][$i] = [];
}

$rule[$NONTERM+$when_clauses][$WHEN] = [
    $WHEN, $value, \&_make_when, $when_values, $R, \&_append_first,
    $block, $when_clauses];
for my $i ($ELSE, $ENDCASE) {
    $rule[$NONTERM+$when_clauses][$i] = [];
}

$rule[$NONTERM+$else_clause][$ELSE] = [
    $ELSE, \&_make_else, $block];
for my $i ($ENDIF, $ENDUNLESS, $ENDFOR, $ENDCASE) {
    $rule[$NONTERM+$else_clause][$i] = [];
}

$rule[$NONTERM+$pipeline][$FILTER] = [
    $FILTER, $IDENT, \&_make_filter, $filter_arguments,
    \&_append, $pipeline];
for my $i ($R, $RR, $RRR) {
    $rule[$NONTERM+$pipeline][$i] = [];
}

$rule[$NONTERM+$filter_arguments][$COLON] = [
    $COLON, $value, \&_append_second, $filter_comma_arguments];
$rule[$NONTERM+$filter_comma_arguments][$COMMA] = [
    $COMMA, $value, \&_append_second, $filter_comma_arguments];
for my $i ($R, $RR, $RRR, $FILTER) {
    $rule[$NONTERM+$filter_arguments][$i] = [];
    $rule[$NONTERM+$filter_comma_arguments][$i] = [];
}

$rule[$NONTERM+$for_list][$LPAREN] = [
    $LPAREN, $value, $RANGE, $value, $RPAREN, \&_for_list_range];
for my $i ($CONST, $IDENT, $STRING, $NUMBER) {
    $rule[$NONTERM+$for_list][$i] = [$value];
}

$rule[$NONTERM+$for_slice][$IDENT] = [
    $IDENT, $COLON, $for_offset, $for_slice];
$rule[$NONTERM+$for_slice][$REVERSED] = [
    $REVERSED, \&_set_for_reversed, $for_slice];
$rule[$NONTERM+$for_slice][$R] = [];

$rule[$NONTERM+$for_offset][$CONTINUE] = [
    $CONTINUE, \&_set_offset_continue];
for my $i ($IDENT, $NUMBER) {
    $rule[$NONTERM+$for_offset][$i] = [$value, \&_set_offset_value];
}

$rule[$NONTERM+$when_values][$OR] = [
    $OR, $value, \&_append_second, $when_values];
$rule[$NONTERM+$when_values][$COMMA] = [
    $COMMA, $value, \&_append_second, $when_values];
$rule[$NONTERM+$when_values][$R] = [];

$rule[$NONTERM+$include_with][$WITH] = [
    $WITH, $variable, \&_include_with];
$rule[$NONTERM+$include_with][$FOR] = [
    $FOR, $variable, \&_include_with];
$rule[$NONTERM+$include_with][$IDENT] = [];
$rule[$NONTERM+$include_with][$R] = [];

$rule[$NONTERM+$include_arguments][$IDENT] = [
    $variable, $COLON, $value, \&_append_include_arguments,
    $include_comma, $include_arguments];
$rule[$NONTERM+$include_arguments][$R] = [];

$rule[$NONTERM+$include_comma][$COMMA] = [$COMMA, \&_ignore];
$rule[$NONTERM+$include_comma][$IDENT] = [];
$rule[$NONTERM+$include_comma][$R] = [];

for my $i ($NOT, $LPAREN, $CONST, $IDENT, $STRING, $NUMBER) {
    $rule[$NONTERM+$expression][$i] = [
        $expression3, $expression2, $expression1];
}

$rule[$NONTERM+$expression1][$OR] = [
    $OR, $expression3, $expression2, \&_make_binary, $expression1];
for my $i ($RPAREN, $R) {
    $rule[$NONTERM+$expression1][$i] = [];
}

$rule[$NONTERM+$expression2][$AND] = [
    $AND, $expression3, \&_make_binary, $expression2];
for my $i ($OR, $RPAREN, $R) {
    $rule[$NONTERM+$expression2][$i] = [];
}

$rule[$NONTERM+$expression3][$LPAREN] = [
    $LPAREN, $expression, $RPAREN, \&_make_subexpressio];
$rule[$NONTERM+$expression3][$NOT] = [
    $NOT, $value, \&_make_unary, $expression4];
for my $i ($CONST, $IDENT, $STRING, $NUMBER) {
    $rule[$NONTERM+$expression3][$i] = [$value, $expression4];
}

$rule[$NONTERM+$expression4][$CMP] = [
    $CMP, $value, \&_make_binary];
for my $i ($AND, $OR, $RPAREN, $R) {
    $rule[$NONTERM+$expression4][$i] = [];
}

$rule[$NONTERM+$value][$IDENT] = [$variable];
$rule[$NONTERM+$value][$CONST] = [$CONST];
$rule[$NONTERM+$value][$STRING] = [$STRING];
$rule[$NONTERM+$value][$NUMBER] = [$NUMBER];

$rule[$NONTERM+$variable][$IDENT] = [
    $IDENT, \&_make_variable, $selectors];

$rule[$NONTERM+$selectors][$DOT] = [
    $DOT, $IDENT, \&_append_second, $selectors];
$rule[$NONTERM+$selectors][$LSQUARE] = [
    $LSQUARE, $value, $RSQUARE, \&_append_second3, $selectors];
for my $i (
    $EQUIV, $IN, $FILTER, $R, $RR, $RRR, $IDENT, $COLON, $WITH, $FOR,
    $OR, $AND, $COMMA, $REVERSED, $RANGE, $RPAREN,
    $RSQUARE, $CMP,
) {
    $rule[$NONTERM+$selectors][$i] = [];
}

sub parse {
    my($class, $source) = @_;
    my $refsrc = \$source;
    my $token_list = _tokenize($refsrc);
    my $next_token = $token_list->[0][0];
    my $output = [[$BEGIN]];
    my @stack = ($block, $EOF);
    while (@stack) {
        my $symbol = shift @stack;
        if (ref $symbol) {
            $symbol->($output);
            next;
        }
        if ($symbol == $EOF) {
            last if $next_token == $EOF;
        }
        elsif ($symbol >= $PLAIN && $symbol <= $RSQUARE) {
            if ($symbol != $next_token) {
                _error($refsrc, $symbol, $token_list->[0]);
            }
            push @{$output}, $token_list->[0][1];
            shift @{$token_list};
            $next_token = $token_list->[0][0];
            next;
        }
        if (my $symbols = $rule[$NONTERM+$symbol][$next_token]) {
            unshift @stack, @{$symbols};
            next;
        }
        _error($refsrc, $symbol, $token_list->[0]);
    }
    return $output->[0];
}

sub _error {
    my($refsrc, $symbol, $token) = @_;
    my $i = $token->[2];
    my $lft = substr ${$refsrc}, 0, $i;
    my $rgt = substr ${$refsrc}, $i;
    my $n = 1 + ($lft =~ tr/\n/\n/);
    my $j = rindex $lft, "\n";
    if (0 <= $j) {
        $lft = substr $lft, $j + 1;
    }
    my $k = index $rgt, "\n";
    if (0 <= $k) {
        $rgt = substr $rgt, 0, $k;
    }
    die qq(SyntaxError: line $n '$lft' ?'$rgt'.\n);
}

## no critic qw(ArgUnpacking FinalReturn)

sub _make_escape {
    my($v0, $v1) = splice @{$_[0]}, -2;
    push @{$_[0]}, [$v0, $v1];
}

sub _make_assign {
    my($v0, $v1, $v2, $v3) = splice @{$_[0]}, -4;
    push @{$_[0]}, [$v0, $v1, $v3];
}

sub _make_unless {
    my $v = pop @{$_[0]};
    $_[0][-2][0] = $IF;
    push @{$_[0]}, [$NOT, $v];
}

sub _make_for {
    my($v0, $v1, $v2, $v3) = splice @{$_[0]}, -4;
    my $node = [$v0];
    push @{$_[0][-1]}, $node;
    push @{$_[0]}, $node;
    my $child = [[$v1, $v3]];
    my $group = join q( ), $v0, _flatten($v3); #_flatten([$v1, $v3]);
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
    push @{$_[0]}, [[$NUMBER, 0], [$CONST, undef], undef, $group];
}

sub _flatten {
    my($array) = @_;
    my @r;
    my @stack = @{$array};
    while (@stack) {
        my $x = shift @stack;
        if (ref $x) {
            unshift @stack, @{$x};
        }
        else {
            push @r, $x;
        }
    }
    return @r;
}

sub _append_for_slice {
    my($v0, $v1) = splice @{$_[0]}, -2;
    push @{$_[0][-1][0]}, @{$v0};
}

sub _make_case {
    my($v0, $v1, $v2) = splice @{$_[0]}, -3;
    my $node = [$v0];
    push @{$_[0][-1]}, $node;
    push @{$_[0]}, $node;
    my $child = [$v1];
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
}

sub _make_capture {
    my($v0, $v1) = splice @{$_[0]}, -2;
    my $node = [$v0];
    push @{$_[0][-1]}, $node;
    push @{$_[0]}, $node;
    my $child = [];
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
    push @{$_[0]}, [$v1];
}

sub _append_increment {
    my($v0, $v1, $v2) = splice @{$_[0]}, -3;
    push @{$_[0][-1]}, [$v0, $v1];
}

sub _append_break {
    my $v0 = pop @{$_[0]};
    push @{$_[0][-1]}, [$v0];
}

sub _make_ifchanged {
    my $node = [pop @{$_[0]}];
    push @{$_[0][-1]}, $node;
    push @{$_[0]}, $node;
}

sub _end_ifchanged { splice @{$_[0]}, -2 }

sub _make_include {
    my($v0, $v1) = splice @{$_[0]}, -2;
    push @{$_[0]}, [$v0, $v1, undef, [], []];
}

sub _make_elsif {
    my $tag = pop @{$_[0]};
    my $child = [];
    pop @{$_[0]}; # drop before child
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
}

sub _make_when {
    my($v0, $v1) = splice @{$_[0]}, -2;
    my $child = [];
    pop @{$_[0]}; # drop before child
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
    push @{$_[0]}, [$v1];
}

sub _make_else {
    my $tag = pop @{$_[0]};
    my $child = [$tag];
    pop @{$_[0]}; # drop before child
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
}

sub _make_filter {
    my($v0, $v1) = splice @{$_[0]}, -2;
    push @{$_[0]}, [$v0, $v1];
}

sub _for_list_range {
    my($v0, $v1, $v2, $v3, $v4) = splice @{$_[0]}, -5;
    push @{$_[0]}, [$v2, $v1, $v3];
}

sub _set_offset_continue {
    my($v0, $v1, $v2) = splice @{$_[0]}, -3;
    if ($v0 eq 'offset') {
        $_[0][-1][0] = [$v2];
    }
}

sub _set_offset_value {
    my($v0, $v1, $v2) = splice @{$_[0]}, -3;
    if ($v0 eq 'offset') {
        $_[0][-1][0] = $v2;
    }
    elsif ($v0 eq 'limit') {
        $_[0][-1][1] = $v2;
    }
}

sub _set_for_reversed {
    $_[0][-1][2] = pop @{$_[0]};
}

sub _include_with {
    my($v0, $v1) = splice @{$_[0]}, -2;
    $_[0][-1][2] = $v1;
}

sub _append_include_arguments {
    my($param, $v1, $arg) = splice @{$_[0]}, -3;
    push @{$_[0][-1][3]}, $param;
    push @{$_[0][-1][4]}, $arg;
}

sub _make_binary {
    my($lhs, $op, $rhs) = splice @{$_[0]}, -3;
    push @{$_[0]}, [$op, $lhs, $rhs];
}

sub _make_subexpression {
    my($v0, $v1, $v2) = splice @{$_[0]}, -3;
    push @{$_[0]}, $v1;
}

sub _make_unary {
    my($op, $lhs) = splice @{$_[0]}, -2;
    push @{$_[0]}, [$op, $lhs];
}

sub _make_variable {
    $_[0][-1] = [$VARIABLE, $_[0][-1]];
}

sub _append {
    my $x = pop @{$_[0]};
    push @{$_[0][-1]}, $x;
}

sub _append_first {
    my($x, $y) = splice @{$_[0]}, -2;
    push @{$_[0][-1]}, $x;
}

sub _append_second {
    my($x, $y) = splice @{$_[0]}, -2;
    push @{$_[0][-1]}, $y;
}

sub _append_second3 {
    my($x, $y, $z) = splice @{$_[0]}, -3;
    push @{$_[0][-1]}, $y;
}

sub _begin_node {
    my $tag = pop @{$_[0]};
    my $node = [$tag];
    push @{$_[0][-1]}, $node;
    push @{$_[0]}, $node;
    my $child = [];
    push @{$_[0][-1]}, $child;
    push @{$_[0]}, $child;
}

sub _end_node { splice @{$_[0]}, -3 }

sub _ignore { pop @{$_[0]} }

## use critic qw(ArgUnpacking FinalReturn)

# $token_list : [[$token_kind, $token_value, pointer(${$refsrc})]]
sub _tokenize {
    my($refsrc) = @_;
    pos(${$refsrc}) = 0;
    my @token_list;
    while (${$refsrc} =~ m{\G(.*?)\{(?:(\{\{?)\s*|%\s*$LMARKUP)}gcomsx) {
        my $plain_value = $1;
        if ($plain_value ne q()) {
            my $i = $LAST_MATCH_START[1];
            push @token_list, [$PLAIN, [$PLAIN, $plain_value], $i];
        }
        my $i = $LAST_MATCH_END[1];
        if (my $tag2 = $2) {
            my $token = $KEYWORD{$tag2 . q[{]};
            push @token_list, [$token, $token, $i];
        }
        elsif (my $tag3 = $3) {
            my $token = $KEYWORD{$tag3};
            push @token_list, [$token, $token, $i];
        }
        elsif (my $tag4 = $4) {
            my $token = $KEYWORD{$tag4};
            push @token_list, [$token, $token, $i];
            next;
        }
        elsif ($5) {   # {%cycle ... %}
            my $group = q();
            if (${$refsrc} =~ m/\G(?:$LSTR|(\w[-\w]*))\s*[:]\s*/gcomsx) {
                $group = $LAST_PAREN_MATCH;
            }
            my @list = ();
            if (${$refsrc} =~ m/\G(?:$LSTR|$LNUM)\s*/gcomsx) {
                push @list, $LAST_PAREN_MATCH;
                while (${$refsrc} =~ m/\G[,]\s*(?:$LSTR|$LNUM)\s*/gcomsx) {
                    push @list, $LAST_PAREN_MATCH;
                }
            }
            if (not ${$refsrc} =~ m/\G%\}\n?/gcomsx or not @list) {
                die "SyntaxError: {%cycle ... %}?\n";
            }
            if ($group eq q()) {
                $group = join q( ), @list;
            }
            $group = 'cycle ' . $group;
            push @token_list, [$CYCLE, [$CYCLE, $group, @list], $i];
            next;
        }
        elsif (defined $6) {   # {%raw%}(.*?){%endraw%}
            my $raw_value = $6;
            if ($raw_value ne q()) {
                push @token_list, [$PLAIN, [$PLAIN, $raw_value], $i];
            }
            next;
        }
        elsif (defined $7) {    # {%comment%}(.*?){%endcomment%}
            next;
        }

        while (${$refsrc} =~ m{\G(?:(%\})\n?|(\}\}\}?)|$LMARKIN\s*)}gcomsx) {
            my $i = $LAST_MATCH_START[0];
            if ($1) {
                push @token_list, [$R, $R, $i];
                last;
            }
            elsif (my $rgt = $2) {
                my $token = $rgt eq q[}}] ? $RR : $RRR;
                push @token_list, [$token, $token, $i];
                last;
            }
            elsif (my $mark = $3) {
                if ($mark eq q[<>]) {
                    $mark = q[!=];
                }
                my $kind = $KEYWORD{$mark};
                my $sym = $kind == $CMP ? $COMPARE{$mark} : $kind;
                push @token_list, [$kind, $sym, $i];
                next;
            }
            elsif (my $word = $4) {
                if (exists $KEYWORD{$word}) {
                    my $kind = $KEYWORD{$word};
                    my $sym = $kind == $CMP ? $COMPARE{$word} : $kind;
                    push @token_list, [$kind, $sym, $i];
                }
                elsif (exists $LCONST{$word}) {
                    push @token_list, [$CONST, [$CONST, $LCONST{$word}], $i];
                }
                else {
                    push @token_list, [$IDENT, $word, $i];
                }
                next;
            }
            elsif (defined $5) {
                my $n = do{ no integer; 0 + $5 };
                push @token_list, [$NUMBER, [$NUMBER, $n], $i];
                next;
            }
            push @token_list, [$STRING, [$STRING, $LAST_PAREN_MATCH], $i];
        }
    }
    my $i = pos ${$refsrc};
    if ($i < (length ${$refsrc})) {
        push @token_list, [$PLAIN, [$PLAIN, substr ${$refsrc}, $i], $i];
    }
    $i = pos ${$refsrc};
    push @token_list, [$EOF, $EOF, $i];
    return \@token_list;
}

sub render {
    my($class, $template, $var, %resources) = @_;
    my $filters = $resources{'filter'} || {};
    my $dir = $resources{'directory'};
    my $string = q();
    my $env = [[{'ifchanged' => q()}, $var || {}, {}]];
    _eval_block(\$string, $template, $env, $filters, $dir);
    return $string;
}

my %XML_SPECIAL = (
    q(&) => '&amp;', q(<) => '&lt;', q(>) => '&gt;', q(") => '&quot;',
    q(') => '&#39;', q(\\) => '&#92;',
);

my @EVAL_BLOCK;
$EVAL_BLOCK[$NOESCAPE] = \&_eval_noescape;
$EVAL_BLOCK[$FOR] = \&_eval_for;
$EVAL_BLOCK[$BREAK] = \&_eval_break;
$EVAL_BLOCK[$CONTINUE] = \&_eval_continue;
$EVAL_BLOCK[$CASE] = \&_eval_case;
$EVAL_BLOCK[$CAPTURE] = \&_eval_capture;
$EVAL_BLOCK[$CYCLE] = \&_eval_cycle;
$EVAL_BLOCK[$IFCHANGED] = \&_eval_ifchanged;
$EVAL_BLOCK[$INCLUDE] = \&_eval_include;
$EVAL_BLOCK[$ASSIGN] = \&_eval_assign;
$EVAL_BLOCK[$DECREMENT] = \&_eval_decrement;
$EVAL_BLOCK[$INCREMENT] = \&_eval_increment;

my $THROW_BREAK = __PACKAGE__ . '::ThrowBreak';
my $THROW_CONTINUE = __PACKAGE__ . '::ThrowContinue';

sub _eval_block {
    my($out, $template, $env, $filters, $dir) = @_;
    my $i = 1;
    while ($i < @{$template}) {
        my $expr = $template->[$i++];
        my $func = $expr->[0];
        if ($func == $PLAIN) {
            ${$out} .= $expr->[1];
            next;
        }
        if ($func == $ESCAPE) {
            my $s = _eval_value_pipeline($expr, 1, $env, $filters);
            $s = defined $s ? $s : q();
            $s =~ s/([&<>"'\\])/$XML_SPECIAL{$1}/egmsx;
            ${$out} .= $s;
            next;
        }
        if ($func == $IF) {
            my $j = 1;
            while ($j < @{$expr}) {
                my $clause = $expr->[$j++];
                if (ref $clause->[0]) {
                    my $c = _eval_expression($clause->[0], $env);
                    next if ! $c;
                }
                _eval_block($out, $clause, $env, $filters, $dir);
                last;
            }
            next;
        }
        $EVAL_BLOCK[$func]->($out, $expr, $env, $filters, $dir);
    }
    return;
}

sub _eval_noescape {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $s = _eval_value_pipeline($expr, 1, $env, $filters);
    $s = defined $s ? $s : q();
    ${$out} .= $s;
    return;
}

sub _eval_for {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $scope = $env->[-1];
    my $for = $expr->[1][0];
    my $list = $for->[1];
    if ($list->[0] == $RANGE) {
        my $from = _eval_value($list->[1], $env);
        my $to = _eval_value($list->[2], $env);
        $list = [$from .. $to];
    }
    else {
        $list = _eval_value($list, $env);
    }
    $list = ! defined $list ? []
           : ! ref $list && $list eq q() ? [] # Liquid way
           : ref $list eq 'HASH' ? [sort keys %{$list}]
           : ref $list ne 'ARRAY' ? [$list]
           : $list;
    my @array = @{$list};
    my $offset = $for->[2];
    my $limit = _eval_value($for->[3], $env);
    my $reversed = $for->[4];
    my $group = $for->[5];
    if ($offset->[0] eq $CONTINUE) {
        $offset = $scope->[0]{$group} ||= 0;
    }
    else {
        $offset = _eval_value($offset, $env);
    }
    if (! $limit) {
        $limit = @array;
    }
    if ($offset >= @array) {
        @array = ();
    }
    else {
        @array = splice @array, $offset, $limit;
    }
    $scope->[0]{$group} = $offset + (scalar @array);
    my $last_index = $#array;
    if ($last_index < 0) {
        if (exists $expr->[2]) {
            _eval_block($out, $expr->[2], $env, $filters, $dir);
        }
        return;
    }
    if ($reversed) {
        @array = reverse @array;
    }
    push @{$scope}, {$for->[0][1] => undef};
    my($ref, $reftype, $slot) = _eval_variable($for->[0], $env);
    for my $i (0 .. $#array) {
        $ref->{$slot} = $array[$i];
        $scope->[-1]{'forloop'} = {
            'index0' => $i,
            'index' => $i + 1,
            'rindex' => $last_index - $i + 1,
            'rindex0' => $last_index - $i,
            'first' => $i == 0,
            'last' => $i == $last_index,
            'length' => $last_index + 1,
        };
        if (! eval{
            _eval_block($out, $expr->[1], $env, $filters, $dir);
            1;
        }) {
            my $e = $@;
            my $reftype = ref $e;
            if ($reftype eq $THROW_BREAK) {
                last;
            }
            elsif ($reftype ne $THROW_CONTINUE) {
                pop @{$scope};
                die $e;
            }
        }
    }
    pop @{$scope};
    return;
}

sub _eval_break {
    my($out, $expr, $env, $filters, $dir) = @_;
    if (exists $env->[-1][-1]{'forloop'}) {
        die bless {}, $THROW_BREAK;
    }
    return;
}

sub _eval_continue {
    my($out, $expr, $env, $filters, $dir) = @_;
    if (exists $env->[-1][-1]{'forloop'}) {
        die bless {}, $THROW_CONTINUE;
    }
    return;
}

sub _eval_case {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $v0 = _eval_value($expr->[1][0], $env);
    if (@{$expr->[1]} > 1) {
        _eval_block($out, $expr->[1], $env, $filters, $dir);
    }
    my $j = 2;
    while ($j < @{$expr}) {
        my $clause = $expr->[$j++];
        if (ref $clause->[0]) {
            my $found;
            for my $alt (@{$clause->[0]}) {
                my $v1 = _eval_value($alt, $env);
                if (_eval_eq($v0, $v1)) {
                    $found = 1;
                    last;
                }
            }
            next if ! $found;
        }
        _eval_block($out, $clause, $env, $filters, $dir);
        last;
    }
    return;
}

sub _eval_cycle {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $group = $expr->[1];
    if (! exists $env->[-1][0]{$group}) {
        $env->[-1][0]{$group} = 2;
    }
    ${$out} .= $expr->[ $env->[-1][0]{$group} ];
    ++$env->[-1][0]{$group};
    if ($env->[-1][0]{$group} > $#{$expr}) {
        $env->[-1][0]{$group} = 2;
    }
    return;
}

sub _eval_ifchanged {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $cap = q();
    _eval_block(\$cap, $expr, $env, $filters, $dir);
    return if $cap eq $env->[-1][0]{'ifchanged'};
    ${$out} .= $cap;
    $env->[-1][0]{'ifchanged'} = $cap;
    return;
}

sub _eval_include {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $name = _eval_value($expr->[1], $env);
    my $forexpr = $expr->[2] || [$VARIABLE, $name];
    my $param = $expr->[3];
    my $argexpr = $expr->[4];
    my $subexpr = $dir->get_template_code($name, $env) or return;
    if (@{$env} > $STACK_LIMIT) {
        croak 'StackFull: stack over.';
    }
    my $for_value = _eval_value($forexpr, $env);
    $for_value = ref $for_value eq 'ARRAY' ? $for_value : [$for_value];
    my @args = map { _eval_value($_, $env) } @{$argexpr};
    for my $name_value (@{$for_value}) {
        push @{$env}, [{'ifchanged' => q()}, {}];
        for my $i (0 .. $#{$param}) {
            my($ref, $reftype, $slot) = _eval_variable($param->[$i], $env);
            $ref->{$slot} = $args[$i];
        }
        $env->[-1][-1]{$name} = $name_value;
        _eval_block($out, $subexpr, $env, $filters, $dir);
        pop @{$env};
    }
    return;
}

sub _eval_assign {
    my($out, $expr, $env, $filters, $dir) = @_;
    my($ref, $reftype, $slot) = _eval_variable($expr->[1], $env);
    my $value = _eval_value_pipeline($expr, 2, $env, $filters);
    if ($reftype eq 'HASH') {
        $ref->{$slot} = $value;
    }
    elsif ($reftype eq 'ARRAY') {
        $ref->[$slot] = $value;
    }
    elsif (eval { $ref->can($slot) }) {
        $ref->$slot($value);
    }
    return;
}

sub _eval_capture {
    my($out, $expr, $env, $filters, $dir) = @_;
    my $cap = q();
    _eval_block(\$cap, $expr->[1], $env, $filters, $dir);
    my $head = $expr->[1][0];
    my $i = 1;
    while ($i < @{$head}) {
        $cap = _eval_filter($cap, $head->[$i++], $env, $filters);
    }
    my($ref, $reftype, $slot) = _eval_variable($head->[0], $env);
    if ($reftype eq 'HASH') {
        $ref->{$slot} = $cap;
    }
    elsif ($reftype eq 'ARRAY') {
        $ref->[$slot] = $cap;
    }
    elsif (eval { $ref->can($slot) }) {
        $ref->$slot($cap);
    }
    return;
}

sub _eval_decrement {
    my($out, $expr, $env, $filters, $dir) = @_;
    my($ref, $reftype, $slot) = _eval_variable($expr->[1], $env);
    if ($reftype eq 'HASH') {
        $ref->{$slot} = ! defined $ref->{$slot} ? 0
            : looks_like_number("$ref->{$slot}") ? $ref->{$slot}
            : 0;
        ${$out} .= --$ref->{$slot};
    }
    elsif ($reftype eq 'ARRAY') {
        $ref->[$slot] = ! defined $ref->[$slot] ? 0
            : looks_like_number("$ref->[$slot]") ? $ref->[$slot]
            : 0;
        ${$out} .= --$ref->[$slot];
    }
    return;
}

sub _eval_increment {
    my($out, $expr, $env, $filters, $dir) = @_;
    my($ref, $reftype, $slot) = _eval_variable($expr->[1], $env);
    if ($reftype eq 'HASH') {
        my $v = $ref->{$slot} = ! defined $ref->{$slot} ? 0
            : looks_like_number("$ref->{$slot}") ? $ref->{$slot}
            : 0;
        ${$out} .= $v;
        ++$ref->{$slot};
    }
    elsif ($reftype eq 'ARRAY') {
        my $v = $ref->[$slot] = ! defined $ref->[$slot] ? 0
            : looks_like_number("$ref->[$slot]") ? $ref->[$slot]
            : 0;
        ${$out} .= $v;
        ++$ref->[$slot];
    }
    return;
}

sub _eval_value_pipeline {
    my($expr, $i, $env, $filters) = @_;
    my $s = _eval_value($expr->[$i++], $env);
    while ($i < @{$expr}) {
        $s = _eval_filter($s, $expr->[$i++], $env, $filters);
    }
    return $s;
}

sub _eval_contains {
    my($lhs, $rhs) = @_;
    my $found = q();
    if (! ref $lhs) {
        $found = 0 <= index $lhs, $rhs;
    }
    elsif (ref $lhs eq 'HASH') {
        $found = exists $lhs->{$rhs};
    }
    elsif (ref $lhs eq 'ARRAY') {
        for (@{$lhs}) {
            next if $_ ne $rhs;
            $found = 1;
            last;
        }
    }
    return $found;
}

sub _eval_value {
    my($expr, $env) = @_;
    # $env = [.., [$stash, $frame0, $frame1, ..]];
    my $type = $expr->[0];
    return $expr->[1] if $type != $VARIABLE;
    my $value = undef;
    my $i = 1;
    my $slot = $expr->[$i++];
    my $scope = $env->[-1];
    my $k = $#{$scope};
    while ($k > 0) {
        if (exists $scope->[$k]{$slot}) {
            $value = $scope->[$k]{$slot};
            last;
        }
        --$k;
    }
    return $value if ! defined $value;
    my $reftype = ref $value;
    while ($i < @{$expr}) {
        my $slot = $expr->[$i++];
        if (! ref $slot) {
            if ($reftype eq 'HASH') {
                $value
                    = exists $value->{$slot} ? $value->{$slot}
                    : $slot eq 'size' ? (scalar keys %{$value})
                    : $slot eq 'empty?' ? 0 == (scalar keys %{$value})
                    : undef;
            }
            elsif ($reftype eq 'ARRAY') {
                $value
                    = $slot eq 'size' ? (scalar @{$value})
                    : $slot eq 'empty?' ? 0 == (scalar @{$value})
                    : $slot eq 'first' ? $value->[0]
                    : $slot eq 'last' ? $value->[-1]
                    : undef;
            }
            elsif (! $reftype) {
                $value
                    = $slot eq 'size' ? length $value
                    : $slot eq 'length' ? length $value
                    : $slot eq 'empty?' ? 0 == length $value
                    : undef;
            }
            else {
                $value = eval { $value->can($slot) } ? $value->$slot : undef;
            }
        }
        else {
            $slot = _eval_value($slot, $env);
            if ($reftype eq 'HASH') {
                $value = $value->{$slot};
            }
            elsif ($reftype eq 'ARRAY') {
                $value = $value->[$slot];
            }
            else {
                $value = undef;
            }
        }
        return $value if ! defined $value;
        $reftype = ref $value;
    }
    return $value;
}

sub _eval_variable {
    my($expr, $env) = @_;
    my $i = 1;
    my $slot = $expr->[$i++];
    my $scope = $env->[-1];
    my $ref = $scope->[-1];
    my $k = $#{$scope};
    while ($k > 0) {
        if (exists $scope->[$k]{$slot}) {
            $ref = $scope->[$k];
            last;
        }
        --$k;
    }
    my $reftype = ref $ref;
    while ($i < @{$expr}) {
        my $slot1 = $slot;
        $slot = $expr->[$i++];
        if (! ref $slot1) {
            if ($reftype eq 'HASH') {
                if (! exists $ref->{$slot1} || ref $ref->{$slot1} ne 'HASH') {
                    $ref->{$slot1} = {};
                }
                $ref = $ref->{$slot1};
            }
            else {
                $ref = eval { $ref->can($slot1) } ? $ref->$slot1 : undef;
            }
        }
        else {
            $slot1 = _eval_value($slot1, $env);
            if ($reftype eq 'HASH') {
                if (! exists $ref->{$slot1} || ref $ref->{$slot1} ne 'HASH') {
                    $ref->{$slot1} = {};
                }
                $ref = $ref->{$slot1};
            }
            elsif ($reftype eq 'ARRAY') {
                if (! exists $ref->[$slot1] || ref $ref->[$slot1] ne 'ARRAY') {
                    $ref->[$slot1] = {};
                }
                $ref = $ref->[$slot1];
            }
            else {
                $ref = undef;
            }
        }
        $reftype = ref $ref;
        last if ! defined $ref;
    }
    if (ref $slot) {
        $slot = _eval_value($slot, $env);
    }
    return ($ref, $reftype, $slot);
}

my @EVAL_EXPRESSION;
$EVAL_EXPRESSION[$EQ-$EQ] = \&_eval_eq;
$EVAL_EXPRESSION[$NE-$EQ] = \&_eval_ne;
$EVAL_EXPRESSION[$LT-$EQ] = \&_eval_lt;
$EVAL_EXPRESSION[$LE-$EQ] = \&_eval_le;
$EVAL_EXPRESSION[$GT-$EQ] = \&_eval_gt;
$EVAL_EXPRESSION[$GE-$EQ] = \&_eval_ge;
$EVAL_EXPRESSION[$CONTAINS-$EQ] = \&_eval_contains;

sub _eval_expression {
    my($expr, $env) = @_;
    my $func = $expr->[0];
    return $expr->[1] if $func <= $NUMBER;
    return _eval_value($expr, $env) if $func == $VARIABLE;
    my $lhs = _eval_expression($expr->[1], $env);
    if ($func == $OR) {
        return $lhs || _eval_expression($expr->[2], $env);
    }
    if ($func == $AND) {
        return $lhs && _eval_expression($expr->[2], $env);
    }
    return ! $lhs if $func == $NOT;
    my $rhs = _eval_expression($expr->[2], $env);
    return $EVAL_EXPRESSION[$func-$EQ]->($lhs, $rhs);
}

sub _eval_eq { return _eval_compare(@_) == 0 }
sub _eval_ne { return _eval_compare(@_) != 0 }
sub _eval_lt { return _eval_compare(@_) == -1 }
sub _eval_gt { return _eval_compare(@_) >  0 }
sub _eval_ge { return _eval_compare(@_) >= 0 }

sub _eval_le {
    my $i = _eval_compare(@_);
    return $i == -1 || $i == 0;
}

no integer;

sub _eval_compare {
    my($lhs, $rhs) = @_;
    return ! defined $lhs && ! defined $rhs ? 0
        : ! defined $lhs || ! defined $rhs ? -2
        : ref $lhs eq 'ARRAY' && ref $rhs eq 'ARRAY'
             && @{$lhs} == 0 && @{$rhs} == 0 ? 0
        : looks_like_number("$lhs") && looks_like_number("$rhs")
        ? ($lhs <=> $rhs) : ($lhs cmp $rhs);    
}

my %STDFILTER = (
    'escape' => \&_filter_escape,
    'h' => \&_filter_escape,
    'escape_once' => \&_filter_escape_once,
    'downcase' => \&_filter_downcase,
    'upcase' => \&_filter_upcase,
    'first' => \&_filter_first,
    'last' => \&_filter_last,
    'sort' => \&_filter_sort,
    'nsort' => \&_filter_nsort,
    'map' => \&_filter_map,
    'size' => \&_filter_size,
    'prepend' => \&_filter_prepend,
    'append' => \&_filter_append,
    'minus' => \&_filter_minus,
    'plus' => \&_filter_plus,
    'times' => \&_filter_times,
    'divided_by' => \&_filter_divided_by,
    'modulo' => \&_filter_modulo,
    'checked' => \&_filter_checked,
    'selected' => \&_filter_selected,
    'split' => \&_filter_split,
    'join' => \&_filter_join,
    'capitalize' => \&_filter_capitalize,
    'attribute' => \&_filter_attribute,
    'strip_html' => \&_filter_strip_html,
    'strip_newlines' => \&_filter_strip_newlines,
    'newline_to_br' => \&_filter_newline_to_br,
    'replace' => \&_filter_replace,
    'replace_first' => \&_filter_replace_first,
    'remove' => \&_filter_remove,
    'remove_first' => \&_filter_remove_first,
    'truncate' => \&_filter_truncate,
    'truncatewords' => \&_filter_truncatewords,
    'date' => \&_filter_date,
);

sub _eval_filter {
    my($s, $expr, $env, $filters) = @_;
    my $name = $expr->[1];
    my $proc = exists $filters->{$name} ? $filters->{$name}
              : exists $STDFILTER{$name} ? $STDFILTER{$name}
              : return " {{ filter_not_found | $name }} ";
    my @arg;
    my $i = 2;
    while ($i < @{$expr}) {
        my $x = _eval_value($expr->[$i++], $env);
        push @arg, $x;
    }
    return $proc->($s, @arg);
}

my %CHECKED = map { $_ => 1 } qw(
    compact nowrap ismap declare noshade checked
    disabled readonly multiple selected noresize defer
);

sub _filter_escape {
    my($s) = @_;
    $s =~ s/([&<>"'\\])/$XML_SPECIAL{$1}/egmsx;
    return $s;
}

sub _filter_escape_once {
    my($s) = @_;
    $s =~ s{
       ([<>"'\\])
    |   &((?:\#(?:x[0-9A-Fa-f]+|[0-9]+)|[A-Za-z][A-Za-z0-9]*);)?
    }{
        $1 ? $XML_SPECIAL{$1} : $2 ? "&$2" : '&amp;'
    }egmsx;
    return $s;
}

sub _filter_downcase { return lc $_[0] }
sub _filter_upcase { return uc $_[0] }
sub _filter_first { return $_[0]->[0] }
sub _filter_last { return $_[0]->[-1] }
sub _filter_sort { return [sort @{$_[0]}] }
sub _filter_nsort { return [sort { $a <=> $b } @{$_[0]}] }
sub _filter_map { return [map { $_->{$_[1]} } @{$_[0]}] }
sub _filter_size { return ! ref $_[0] ? length $_[0] : $#{$_[0]} + 1 }
sub _filter_prepend { return $_[1] . $_[0] }
sub _filter_append { return $_[0] . $_[1] }
sub _filter_minus { return $_[0] - $_[1] }
sub _filter_plus { return $_[0] + $_[1] }
sub _filter_times { return $_[0] * $_[1] }
sub _filter_divided_by { return int $_[0] / $_[1] }
sub _filter_modulo { return $_[0] % $_[1] }
sub _filter_checked { return _filter_attribute($_[0], 'checked') }
sub _filter_selected { return _filter_attribute($_[0], 'selected') }

sub _filter_split {
    my($s, $f) = @_;
    $f = quotemeta $f;
    return [split /$f/msx, $s, -1];
}

sub _filter_join {
    my($a, $f) = @_;
    $f = ! defined $f ? q( ) : $f;
    return join $f, @{$a};
}

sub _filter_capitalize {
    my($s) = @_;
    $s =~ s{(\w+)}{ ucfirst $1 }egmsx;
    return $s;
}

sub _filter_attribute {
    my($v, $k) = @_;
    my @attr;
    if (ref $v eq 'ARRAY') {
        $v = join q( ), @{$v};
    }
    if ($CHECKED{$k}) {
        if ($v && 'false' ne lc $v) {
            push @attr, $k . q(=") . $k . q(");
        }
    }
    else {
        if ($k eq 'href' || $k eq 'src' || 0 <= index $k, 'resource') {
            if (utf8::is_utf8($v)) {
                require Encode;
                $v = Encode::encode_utf8($v);
            }
            $v =~ s{(%[[:xdigit:]]{2})|([^\w\-=/,.:;?\#\$\&])}{
                $1 ? $1 : sprintf '%%%02X', ord $2
            }egmsx;
        }
        $v = $k eq 'value' ? _filter_escape($v) : _filter_escape_once($v);
        push @attr, _filter_escape_once($k) . q(=") . $v . q(");
    }
    return join q(), @attr;
}

sub _filter_strip_html {
    my($s) = @_;
    $s =~ s{<(?:script.*?</script|style.*?</style)?[^>]*>}{}gimsx;
    return $s;
}

sub _filter_strip_newlines {
    my($s) = @_;
    $s =~ s{(?:\r\n?|\n)+}{}gmsx;
    return $s;
}

sub _filter_newline_to_br {
    my($s) = @_;
    $s =~ s{(\r\n?|\n)}{<br />$1}gmsx;
    return $s;
}

sub _filter_replace {
    my($s, $f, $t) = @_;
    $f = quotemeta $f;
    $s =~ s{$f}{$t}gmsx;
    return $s;
}

sub _filter_replace_first {
    my($s, $f, $t) = @_;
    $f = quotemeta $f;
    $s =~ s{$f}{$t}msx;
    return $s;
}

sub _filter_remove {
    my($s, $f) = @_;
    $f = quotemeta $f;
    $s =~ s{$f}{}gmsx;
    return $s;
}

sub _filter_remove_first {
    my($s, $f, $t) = @_;
    $f = quotemeta $f;
    $s =~ s{$f}{}msx;
    return $s;
}

sub _filter_truncate {
    my($s, $n) = @_;
    return $s if ! defined $n || $n >= length $s;
    return '...' if $n < 4;
    return substr ($s, 0, $n - 3) . '...';
}

sub _filter_truncatewords {
    my($s, $n) = @_;
    return $s if ! defined $n;
    return '...' if $n < 1;
    my $m = $n - 1;
    my($t) = $s =~ m/(\w+(?:\W*\w+){0,$m})/msx;
    return $s eq $t ? $s : $t . '...';
}

sub _filter_date {
    my($s, $fmt) = @_;
    $fmt = ! defined $fmt || $fmt eq q() ? '%F %T' : $fmt;
    require Encode;
    require POSIX;
    require Time::Piece;
    return undef if ! defined $s; ## no critic qw(ExplicitReturnUndef)
    my $epoch
        = ref $s && eval { $s->can('epoch') } ? $s->epoch
        : ref $s ? return $s
        : defined $s && $s eq 'now' ? time
        : undef;
    if (! defined $epoch && $s =~ m{\A\s*
        ([0-9]+)[-/]([0-9]+)[-/]([0-9]+)
        (?:(?:T|\s+)([0-9]+)[:]([0-9]+)(?:[:]([0-9]+)(?:[.][0-9]+)?)?)?
        (?:\s*(Z|UTC|GMT|[+-]00[:]?00))?
        \s*
    \z}msx) {
        my $s1 = sprintf '%04d-%02d-%02dT%02d:%02d:%02d',
            $1, $2, $3, $4 || 0, $5 ||0, $6 || 0;
        my $tpiece = defined $7 ? Time::Piece->gmtime : Time::Piece->localtime;
        $epoch = $tpiece->strptime($s1, '%Y-%m-%dT%H:%M:%S')->epoch;
    }
    elsif (! defined $epoch && looks_like_number($s)) {
        $epoch = $s;
    }
    else {
        return $s;
    }
    my $time = $fmt =~ m/Z|UTC|GMT|[+-]00[:]?00/msx
        ? Time::Piece->gmtime($epoch) : Time::Piece->localtime($epoch);
    my $is_utf8 = utf8::is_utf8($fmt);
    if ($is_utf8) {
        $fmt = Encode::encode('UTF-8', $fmt);
    }
    my $loc = POSIX::setlocale(POSIX::LC_TIME(), q());
    POSIX::setlocale(POSIX::LC_TIME(), 'C');
    my $t = $time->strftime($fmt);
    POSIX::setlocale(POSIX::LC_TIME(), $loc);
    if ($is_utf8) {
        $t = Encode::decode('UTF-8', $t);
    }
    return $t;
}

1;

__END__

=pod

=head1 NAME

Text::Liq - Liquid markup template processor.

=head1 VERSION

0.01

=head1 SYNOPSIS

    use Text::Liq;
    
    my $liquid_content = <<'EOS';
    {% for entry in entries %}
    <article id="{{ entry.id }}">
      <h1>{{ entry.title }}</h1>
      <div class="posted">{{ entry.posted | date:'%Y-%m-%d %H:%M' }}</div>
      {{{ entry.content }}}
    <article>
    {% endfor %}
    EOS
    my $template = Text::Liq->parse($liquid_content);
    my $html = Text::Liq->render($template, {
        'entries' => [
            {'title' => 'Liq markups',
             'posted' => '2013-03-25T22:33:44',
             'content' => '...'},
            {'title' => 'Liq markups grammary',
             'posted' => '2013-03-25T21:32:44',
             'content' => '...'},
        ],
    });

=head1 DESCRIPTION

=head1 METHODS 

=over

=item C<< Text::Liq->parse($liquid_content_string) >>

Parses a given Liquid markup content and converts to a tree.

=item C<< Text::Liq->render($compiled_code, \%param, %resources) >>

Runs the parsed template tree with parameters, and optional filter suits.
Optional resources take

    'filter' => {
        'myfilter' => sub {
            my($string, $arg1, $arg2) = @_;
            # some processing in $string
            return $string;
        },
    },
    'directory' => LocalDirectory->new('/var/httpd/app/liquid-root/'),

=back

=head1 DEPENDENCIES

L<Scalar::Util>, L<Time::Piece>, L<Encode>

=head1 SEE ALSO

L<http://liquidmarkup.org/> - Ruby's Liquid markups.
L<Template::Liquid> - Another Perl implementation.

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

