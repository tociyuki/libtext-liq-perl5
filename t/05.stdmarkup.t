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

=== unliq statement
--- input
this text should come out of the template without change...
--- param
+{}
--- expected
this text should come out of the template without change...

=== unliq xml markup
--- input
<blah>
--- param
+{}
--- expected
<blah>

=== unliq marks
--- input
|,.:
--- param
+{}
--- expected
|,.:

=== unliq multilines
--- input
this shouldnt see any transformation either but has multiple lines
     as you can clearly see here ...
--- param
+{}
--- expected
this shouldnt see any transformation either but has multiple lines
     as you can clearly see here ...

=== comment
--- input
the comment block should be removed {%comment%} be gone.. {%endcomment%} .. right?
--- param
+{}
--- expected
the comment block should be removed  .. right?

=== comment 1
--- input
<tt>{%comment%}{%endcomment%}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment 2
--- input
<tt>{%comment%}{% endcomment %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment 3
--- input
<tt>{% comment %}{%endcomment%}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment 4
--- input
<tt>{% comment %}{% endcomment %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment 5
--- input
<tt>{%comment%}comment{%endcomment%}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment 6
--- input
<tt>{% comment %}comment{% endcomment %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== comment foobar 1
--- input
<tt>foo{%comment%}comment{%endcomment%}bar</tt>
--- param
+{}
--- expected
<tt>foobar</tt>

=== comment foobar 2
--- input
<tt>foo{% comment %}comment{% endcomment %}bar</tt>
--- param
+{}
--- expected
<tt>foobar</tt>

=== comment foobar 3
--- input
<tt>foo{%comment%} comment {%endcomment%}bar</tt>
--- param
+{}
--- expected
<tt>foobar</tt>

=== comment foobar 4
--- input
<tt>foo{% comment %} comment {% endcomment %}bar</tt>
--- param
+{}
--- expected
<tt>foobar</tt>

=== comment foo bar 5
--- input
<tt>foo {%comment%} {%endcomment%} bar</tt>
--- param
+{}
--- expected
<tt>foo  bar</tt>

=== comment foo bar 6
--- input
<tt>foo {%comment%}comment{%endcomment%} bar</tt>
--- param
+{}
--- expected
<tt>foo  bar</tt>

=== comment foo bar 7
--- input
<tt>foo {%comment%} comment {%endcomment%} bar</tt>
--- param
+{}
--- expected
<tt>foo  bar</tt>

=== comment foo bar 8
--- input
<tt>foo {%comment%}
  comment
  {%endcomment%} bar</tt>
--- param
+{}
--- expected
<tt>foo  bar</tt>

=== assign
--- input
<tt>var2:{{var2}} {%assign var2 = var%} var2:{{var2}}</tt>
--- param
+{'var' => 'content'}
--- expected
<tt>var2:  var2:content</tt>

=== hyphenated assign
--- SKIP
the Text::Liq's identifier is not arrow hyphenations.
--- input
<tt>a-b:{{a-b}} {%assign a-b = 2 %}a-b:{{a-b}}</tt>
--- param
+{'a-b' => 1}
--- expected
<tt>a-b:1 a-b:2</tt>

=== hyphenated assign in slot
--- input
<tt>a-b:{{var['a-b']}} {%assign var['a-b'] = 2 %}a-b:{{var['a-b']}}</tt>
--- param
+{'var' => {'a-b' => 1}}
--- expected
<tt>a-b:1 a-b:2</tt>

=== assign with colon and spaces in slot
--- input
<tt>{%assign var2 = var["a:b c"].paged %}var2: {{var2}}</tt>
--- param
+{'var' => {'a:b c' => {'paged' => '1' }}}
--- expected
<tt>var2: 1</tt>

=== capture
--- input
<tt>{{ var2 }}{% capture var2 %}{{ var }} foo {% endcapture %}{{ var2 }}{{ var2 }}</tt>
--- param
+{'var' => 'content'}
--- expected
<tt>content foo content foo </tt>

=== case condition 2
--- input
<tt>{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}</tt>
--- param
+{'condition' => 2}
--- expected
<tt> its 2 </tt>

=== case condition 1
--- input
<tt>{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}</tt>
--- param
+{'condition' => 1}
--- expected
<tt> its 1 </tt>

=== case condition 3
--- input
<tt>{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}</tt>
--- param
+{'condition' => 3}
--- expected
<tt></tt>

=== case condition 'string here'
--- input
<tt>{% case condition %}{% when "string here" %} hit {% endcase %}</tt>
--- param
+{'condition' => 'string here'}
--- expected
<tt> hit </tt>

=== case condition 'bad string here'
--- input
<tt>{% case condition %}{% when "string here" %} hit {% endcase %}</tt>
--- param
+{'condition' => 'bad string here'}
--- expected
<tt></tt>

=== case else condition 5
--- input
<tt>{% case condition %}{% when 5 %} hit {% else %} else {% endcase %}</tt>
--- param
+{'condition' => 5}
--- expected
<tt> hit </tt>

=== case else condition 6
--- input
<tt>{% case condition %}{% when 5 %} hit {% else %} else {% endcase %}</tt>
--- param
+{'condition' => 6}
--- expected
<tt> else </tt>

=== case else condition 6'
--- input
<tt>{% case condition %} {% when 5 %} hit {% else %} else {% endcase %}</tt>
--- param
+{'condition' => 6}
--- expected
<tt>  else </tt>

=== case on size 0
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt></tt>

=== case on size 1
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}</tt>
--- param
+{'a' => [1]}
--- expected
<tt>1</tt>

=== case on size 2
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}</tt>
--- param
+{'a' => [1,1]}
--- expected
<tt>2</tt>

=== case on size 3
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}</tt>
--- param
+{'a' => [1,1,1]}
--- expected
<tt></tt>

=== case else on size 0
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt>else</tt>

=== case on size 1
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}</tt>
--- param
+{'a' => [1]}
--- expected
<tt>1</tt>

=== case on size 2
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}</tt>
--- param
+{'a' => [1,1]}
--- expected
<tt>2</tt>

=== case on size 3
--- input
<tt>{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}</tt>
--- param
+{'a' => [1,1,1]}
--- expected
<tt>else</tt>

=== case on empty
--- input
<tt>{% case a.empty? %}{% when true %}true{% when false %}false{% else %}else{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt>true</tt>

=== case on false
--- input
<tt>{% case false %}{% when true %}true{% when false %}false{% else %}else{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt>false</tt>

=== case on true
--- input
<tt>{% case true %}{% when true %}true{% when false %}false{% else %}else{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt>true</tt>

=== case on null
--- input
<tt>{% case null %}{% when true %}true{% when false %}false{% else %}else{% endcase %}</tt>
--- param
+{'a' => []}
--- expected
<tt>else</tt>

=== case shopify 1
--- input
{% case collection.handle %}
{% when 'menswear-jackets' %}
{%   assign ptitle = 'menswear' %}
{% when 'menswear-t-shirts' %}
{%   assign ptitle = 'menswear' %}
{% else %}
{%   assign ptitle = 'womenswear' %}
{% endcase %}
<tt>{{ ptitle }}</tt>
--- param
+{'collection' => {'handle' => 'menswear-jackets'}}
--- expected
<tt>menswear</tt>

=== case shopify 2
--- input
{% case collection.handle %}
{% when 'menswear-jackets'%}
{%   assign ptitle = 'menswear' %}
{% when 'menswear-t-shirts' %}
{%   assign ptitle = 'menswear' %}
{% else %}
{%   assign ptitle = 'womenswear' %}
{% endcase %}
<tt>{{ ptitle }}</tt>
--- param
+{'collection' => {'handle' => 'menswear-t-shirts'}}
--- expected
<tt>menswear</tt>

=== case shopify 3
--- input
{% case collection.handle %}
{% when 'menswear-jackets' %}
{%   assign ptitle = 'menswear' %}
{% when 'menswear-t-shirts' %}
{%   assign ptitle = 'menswear' %}
{% else %}
{%   assign ptitle = 'womenswear' %}
{% endcase %}
<tt>{{ ptitle }}</tt>
--- param
+{'collection' => {'handle' => 'x'}}
--- expected
<tt>womenswear</tt>

=== case shopify 4
--- input
{% case collection.handle %}
{% when 'menswear-jackets' %}
{%   assign ptitle = 'menswear' %}
{% when 'menswear-t-shirts' %}
{%   assign ptitle = 'menswear' %}
{% else %}
{%   assign ptitle = 'womenswear' %}
{% endcase %}
<tt>{{ ptitle }}</tt>
--- param
+{'collection' => {'handle' => 'y'}}
--- expected
<tt>womenswear</tt>

=== case shopify 5
--- input
{% case collection.handle %}
{% when 'menswear-jackets' %}
{%   assign ptitle = 'menswear' %}
{% when 'menswear-t-shirts' %}
{%   assign ptitle = 'menswear' %}
{% else %}
{%   assign ptitle = 'womenswear' %}
{% endcase %}
<tt>{{ ptitle }}</tt>
--- param
+{'collection' => {'handle' => 'z'}}
--- expected
<tt>womenswear</tt>

=== case when or 1
--- input
<tt>{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 1}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or 2
--- input
<tt>{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 2}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or 3
--- input
<tt>{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 3}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or 4
--- input
<tt>{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 4}
--- expected
<tt> its 4 </tt>

=== case when or 5
--- input
<tt>{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 5}
--- expected
<tt></tt>

=== case when or 1
--- input
<tt>{% case condition %}{% when 1 or "string" or null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 1}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or 'string'
--- input
<tt>{% case condition %}{% when 1 or "string" or null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 'string'}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or undef
--- input
<tt>{% case condition %}{% when 1 or "string" or null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => undef}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when or something else
--- input
<tt>{% case condition %}{% when 1 or "string" or null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 'something else'}
--- expected
<tt></tt>

=== case when comma 1
--- input
<tt>{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 1}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma 2
--- input
<tt>{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 2}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma 3
--- input
<tt>{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 3}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma 4
--- input
<tt>{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 4}
--- expected
<tt> its 4 </tt>

=== case when comma 5
--- input
<tt>{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 5}
--- expected
<tt></tt>

=== case when comma 1
--- input
<tt>{% case condition %}{% when 1, "string", null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 1}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma 'string'
--- input
<tt>{% case condition %}{% when 1, "string", null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 'string'}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma undef
--- input
<tt>{% case condition %}{% when 1, "string", null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => undef}
--- expected
<tt> its 1 or 2 or 3 </tt>

=== case when comma something else
--- input
<tt>{% case condition %}{% when 1, "string", null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}</tt>
--- param
+{'condition' => 'something else'}
--- expected
<tt></tt>

=== assign
--- input
<tt>{% assign a = "variable"%}{{a}}</tt>
--- param
+{}
--- expected
<tt>variable</tt>

=== assign global
--- input
<tt>{%for i in (1..2) %}{% assign a = "variable"%}{% endfor %}{{a}}</tt>
--- param
+{'a' => 'foo'}
--- expected
<tt>variable</tt>

=== cycle default group one
--- input
<tt>{%cycle "one", "two"%}</tt>
--- param
+{}
--- expected
<tt>one</tt>

=== cycle default group one two
--- input
<tt>{%cycle "one", "two"%} {%cycle "one", "two"%}</tt>
--- param
+{}
--- expected
<tt>one two</tt>

=== cycle default group empty two
--- input
<tt>{%cycle "", "two"%} {%cycle "", "two"%}</tt>
--- param
+{}
--- expected
<tt> two</tt>

=== cycle default group one two one
--- input
<tt>{%cycle "one", "two" %} {%cycle "one", "two" %} {%cycle "one", "two" %}</tt>
--- param
+{}
--- expected
<tt>one two one</tt>

=== cycle left right
--- input
<tt>{%cycle "text-align: left", "text-align: right" %} {%cycle "text-align: left", "text-align: right" %}</tt>
--- param
+{}
--- expected
<tt>text-align: left text-align: right</tt>

=== cycle multiple
--- input
<tt>{%cycle 1,2 %} {%cycle 1,2 %} {%cycle 1,2 %} {%cycle 1,2,3 %} {%cycle 1,2,3 %} {%cycle 1,2,3 %} {%cycle 1,2,3 %}</tt>
--- param
+{}
--- expected
<tt>1 2 1 1 2 3 1</tt>

=== cycle group multiple
--- input
<tt>{%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %} {%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %} {%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %}</tt>
--- param
+{}
--- expected
<tt>one one two two one one</tt>

=== cycle group multiple 2
--- input
<tt>{%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %} {%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %} {%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %}</tt>
--- param
+{'var1' => 1, 'var2' => 1}
--- expected
<tt>one one two two one one</tt>

=== size of array
--- input
<tt>array has {{ array.size }} elements</tt>
--- param
+{'array' => [1, 2, 3, 4]}
--- expected
<tt>array has 4 elements</tt>

=== size of hash
--- input
<tt>hash has {{ hash.size }} elements</tt>
--- param
+{'hash' => {'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4}}
--- expected
<tt>hash has 4 elements</tt>

=== true is not empty
--- input
<tt>{% if true == empty %}?{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== true is not null
--- input
<tt>{% if true == null %}?{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== empty is not null
--- input
<tt>{% if empty == null %}?{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== ifchanged 1 1 2 2 3 3
--- input
<tt>{%for item in array%}{%ifchanged%}{{item}}{% endifchanged %}{%endfor%}</tt>
--- param
+{'array' => [1, 1, 2, 2, 3, 3]}
--- expected
<tt>123</tt>

=== ifchanged 1 1 1 1
--- input
<tt>{%for item in array%}{%ifchanged%}{{item}}{% endifchanged %}{%endfor%}</tt>
--- param
+{'array' => [1, 1, 1, 1]}
--- expected
<tt>1</tt>

