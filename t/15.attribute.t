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

=== scalar variable
--- input
<input name="foo" type="text" {{{ foo | attribute:'value' }}} />
--- param
+{'foo' => 'content'}
--- expected
<input name="foo" type="text" value="content" />

=== array variable
--- input
<input name="foo" type="text" {{{ foo | attribute:'value' }}} />
--- param
+{'foo' => ['a', 'b', 'c']}
--- expected
<input name="foo" type="text" value="a b c" />

=== escape value
--- input
<input name="foo" type="text" {{{ foo | attribute:'value' }}} />
--- param
+{'foo' => '&<>"&amp;'}
--- expected
<input name="foo" type="text" value="&amp;&lt;&gt;&quot;&amp;amp;" />

=== escape_once without value
--- input
<input name="foo" type="text" {{{ foo | attribute:'title' }}} />
--- param
+{'foo' => '&<>"&amp;'}
--- expected
<input name="foo" type="text" title="&amp;&lt;&gt;&quot;&amp;" />

=== uri escape and escape_once src
--- input
<img {{{ src | attribute:'src' }}} />
--- param
+{'src' => q(/img/<hoge>?rv=1&ty=jpeg)}
--- expected
<img src="/img/%3Choge%3E?rv=1&amp;ty=jpeg" />

=== uri escape and escape_once href
--- input
<a {{{ page | attribute:'href' }}}>
--- param
+{'page' => q(/entry/<hoge>?rv=1&ty=markup#p1)}
--- expected
<a href="/entry/%3Choge%3E?rv=1&amp;ty=markup#p1">

=== boolean checked
--- input
<input name="foo" type="checkbox" {{{ foo | checked }}} />
<input name="bar" type="checkbox" {{{ bar | checked }}} />
--- param
+{'foo' => 1, 'bar' => q()}
--- expected
<input name="foo" type="checkbox" checked="checked" />
<input name="bar" type="checkbox"  />

=== boolean selected
--- input
<input name="foo" type="text" {{{ foo | selected }}} />
<input name="bar" type="text" {{{ bar | selected }}} />
--- param
+{'foo' => 1, 'bar' => q()}
--- expected
<input name="foo" type="text" selected="selected" />
<input name="bar" type="text"  />

