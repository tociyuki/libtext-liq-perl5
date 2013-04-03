use strict;
use warnings;
use Text::Liq;
use Test::Base;

filters {
    'input' => [qw(chomp)],
    'expected' => [qw(chomp)],
    'param' => [qw(eval)],
};

plan tests => 1 * blocks;

run {
    my($block) = @_;
    my $liq = Text::Liq->parse($block->input);
    my $got = Text::Liq->render($liq, $block->param);
    is $got, $block->expected, $block->name;
};

__END__

=== increment
--- input
<tt>{%increment port %}</tt>
--- param
+{}
--- expected
<tt>0</tt>

=== increment twice
--- input
<tt>{%increment port %} {%increment port %}</tt>
--- param
+{}
--- expected
<tt>0 1</tt>

=== increment mix
--- input
<tt>{% increment port %} {% increment starboard %} {% increment port %} {% increment port %} {% increment starboard %}</tt>
--- param
+{}
--- expected
<tt>0 0 1 2 1</tt>

=== decrement
--- input
<tt>{%decrement port %}</tt>
--- param
+{'port' => 10}
--- expected
<tt>9</tt>

=== decrement twice
--- input
<tt>{%decrement port %} {%decrement port %}</tt>
--- param
+{}
--- expected
<tt>-1 -2</tt>

=== increment decrement mix
--- input
<tt>{%increment port %} {%increment starboard%} {%increment port %} {%decrement port%} {%decrement starboard %}</tt>
--- param
+{'port' => 1, 'starboard' => 5}
--- expected
<tt>1 5 2 2 5</tt>

