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

=== capture unliq
--- input
<tt>{% capture var %}test string{% endcapture %}</tt>
<tt>{{ var }}</tt>
--- param
+{}
--- expected
<tt></tt>
<tt>test string</tt>

=== capture in if-statement
--- input
{% assign var = '' %}
{% if true %}
{% capture var %}first-if-statement{% endcapture %}
{% endif %}
{% if true %}
{% capture var %}test-string{% endcapture %}{% endif %}
<tt>{{var}}</tt>
--- param
+{}
--- expected
<tt>test-string</tt>

=== capture in for-statement
--- input
{% assign first = '' %}
{% assign second = '' %}
{% for number in (1..3) %}
{% capture first %}{{number}}{% endcapture %}
{% assign second = first %}
{% endfor %}
<tt>{{ first }}-{{ second }}</tt>
--- param
+{}
--- expected
<tt>3-3</tt>

=== break in capture in for-statement
--- input
{% assign x = '' %}
{% for number in (1..2) %}
{% capture x %}abc{%break%}def{% endcapture %}
{% endfor %}
<tt>{{ x }}</tt>
--- param
+{}
--- expected
<tt></tt>

