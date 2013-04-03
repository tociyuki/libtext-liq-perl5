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

=== unless true
--- input
<tt>{% unless true %} this text should not go into the output {% endunless %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== unless false
--- input
<tt>{% unless false %} this text should go into the output {% endunless %}</tt>
--- param
+{}
--- expected
<tt> this text should go into the output </tt>

=== unless true end unless false end
--- input
<tt>{% unless true %} you suck {% endunless %} {% unless false %} you rock {% endunless %}?</tt>
--- param
+{}
--- expected
<tt>  you rock ?</tt>

=== unless true else
--- input
<tt>{% unless true %} THEN {%else %} ELSE {% endunless %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== unless false else
--- input
<tt>{% unless false %} THEN {%else %} ELSE {% endunless %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== for unless end end
--- input
<tt>{% for i in choices %}{% unless i %}{{ forloop.index }}{% endunless %}{% endfor %}</tt>
--- param
+{'choices' => [1, undef, 1!=1]}
--- expected
<tt>23</tt>

=== for unless else end end
--- input
<tt>{% for i in choices %}{% unless i %} {{ forloop.index }} {% else %} TRUE {% endunless %}{% endfor %}</tt>
--- param
+{'choices' => [1, undef, 1!=1]}
--- expected
<tt> TRUE  2  3 </tt>

