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

=== array[0]
--- input
{% assign foo = values %}.{{ foo[0] }}.
--- param
+{'values' => [qw(foo bar baz)]}
--- expected
.foo.

=== array[1]
--- input
{% assign foo = values %}.{{ foo[1] }}.
--- param
+{'values' => [qw(foo bar baz)]}
--- expected
.bar.

=== filter[1]
--- input
{% assign foo = values | split: "," %}.{{ foo[1] }}.
--- param
+{'values' => 'foo,bar,baz'}
--- expected
.bar.
