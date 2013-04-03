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

=== markup
--- input
<tt>{% raw %}{% comment %} test {% endcomment %}{% endraw %}</tt>
--- param
+{}
--- expected
<tt>{% comment %} test {% endcomment %}</tt>

=== markup escape
--- input
<tt>{% raw %}{{ test }}{% endraw %}</tt>
--- param
+{}
--- expected
<tt>{{ test }}</tt>

