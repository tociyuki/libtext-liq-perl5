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

=== yo  yo  yo  yo
--- input
<tt>{%for item in array%} yo {%endfor%}</tt>
--- param
+{'array' => [1,2,3,4]}
--- expected
<tt> yo  yo  yo  yo </tt>

=== yoyo
--- input
<tt>{%for item in array%}yo{%endfor%}</tt>
--- param
+{'array' => [1,2]}
--- expected
<tt>yoyo</tt>

=== yo
--- input
<tt>{%for item in array%} yo {%endfor%}</tt>
--- param
+{'array' => [1]}
--- expected
<tt> yo </tt>

=== silent
--- input
<tt>{%for item in array%}{%endfor%}</tt>
--- param
+{'array' => [1,2]}
--- expected
<tt></tt>

=== silent
--- input
<pre>
{%for item in array%}
  yo
{%endfor%}
</pre>
--- param
+{'array' => [1,2,3]}
--- expected
<pre>
  yo
  yo
  yo
</pre>

=== reversed
--- input
<tt>{%for item in array reversed%}{{item}}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt>321</tt>

=== range
--- input
<tt>{%for item in (1..3) %} {{item}} {%endfor%}</tt>
--- param
+{}
--- expected
<tt> 1  2  3 </tt>

=== array
--- input
<tt>{%for item in array%} {{item}} {%endfor%}</tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt> 1  2  3 </tt>

=== array w/o space
--- input
<tt>{%for item in array%}{{item}}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt>123</tt>

=== array space
--- input
<tt>{% for item in array %}{{item}}{% endfor %}</tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt>123</tt>

=== array abcd
--- input
<tt>{% for item in array %}{{item}}{% endfor %}</tt>
--- param
+{'array' => ['a', 'b', 'c', 'd']}
--- expected
<tt>abcd</tt>

=== array a ' ' b ' ' c
--- input
<tt>{% for item in array %}{{item}}{% endfor %}</tt>
--- param
+{'array' => ['a', ' ', 'b', ' ', 'c']}
--- expected
<tt>a b c</tt>

=== array a '' b '' c
--- input
<tt>{% for item in array %}{{item}}{% endfor %}</tt>
--- param
+{'array' => ['a', '', 'b', '', 'c']}
--- expected
<tt>abc</tt>

=== forloop.index/forloop.length
--- input
<tt>{%for item in array%} {{forloop.index}}/{{forloop.length}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 1/3  2/3  3/3 </tt>

=== forloop.index
--- input
<tt>{%for item in array%} {{forloop.index}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 1  2  3 </tt>

=== forloop.index0
--- input
<tt>{%for item in array%} {{forloop.index0}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 0  1  2 </tt>

=== forloop.rindex0
--- input
<tt>{%for item in array%} {{forloop.rindex0}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 2  1  0 </tt>

=== forloop.rindex
--- input
<tt>{%for item in array%} {{forloop.rindex}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 3  2  1 </tt>

=== forloop.first
--- input
<tt>{%for item in array%} {{forloop.first}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt> 1     </tt>

=== forloop.last
--- input
<tt>{%for item in array%} {{forloop.last}} {%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt>     1 </tt>

=== if forloop.first
--- input
<tt>{%for item in array%}{% if forloop.first %}+{% else %}-{% endif %}{%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt>+--</tt>

=== if forloop.last
--- input
<tt>{%for item in array%}{% if forloop.last %}+{% else %}-{% endif %}{%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt>--+</tt>

=== for else 1
--- input
<tt>{%for item in array%}+{% else %}-{%endfor%}</tt>
--- param
+{'array' => ['a', 'b', 'c']}
--- expected
<tt>+++</tt>

=== for else []
--- input
<tt>{%for item in array%}+{% else %}-{%endfor%}</tt>
--- param
+{'array' => []}
--- expected
<tt>-</tt>

=== for else undef
--- input
<tt>{%for item in array%}+{% else %}-{%endfor%}</tt>
--- param
+{'array' => undef}
--- expected
<tt>-</tt>

=== for limit:2
--- input
<tt>{%for i in array limit:2 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>12</tt>

=== for limit:4
--- input
<tt>{%for i in array limit:4 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>1234</tt>

=== for limit:4 offset:2
--- input
<tt>{%for i in array limit:4 offset:2 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>3456</tt>

=== for offset:2 limit:4 
--- input
<tt>{%for i in array offset:2 limit:4 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>3456</tt>

=== for limit: 4 offset: 2
--- input
<tt>{%for i in array limit: 4 offset: 2 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>3456</tt>

=== for limit: var offset: var
cannot use variable name limit and offset.
--- input
<tt>{%for i in array limit: n offset: m %}{{ i }}{%endfor%}</tt>
--- param
+{
    'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0],
    'n' => 4,
    'm' => 2,
}
--- expected
<tt>3456</tt>

=== for in for
--- input
<tt>{%for item in array%}{%for i in item%}{{ i }}{%endfor%}{%endfor%}</tt>
--- param
+{'array' => [[1,2],[3,4],[5,6]]}
--- expected
<tt>123456</tt>

=== for offset: 7
--- input
<tt>{%for i in array offset: 7 %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}
--- expected
<tt>890</tt>

=== for offset:continue
--- input
<pre>
{%for i in array.items limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 %}
{{i}}
{%endfor%}
</pre>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}}
--- expected
<pre>
1
2
3
next
4
5
6
next
7
8
9
</pre>

=== for offset:continue limit
--- input
<pre>
{%for i in array.items limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:1 %}
{{i}}
{%endfor%}
</pre>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}}
--- expected
<pre>
1
2
3
next
4
5
6
next
7
</pre>

=== for offset:continue big limit
--- input
<pre>
{%for i in array.items limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:1000 %}
{{i}}
{%endfor%}
</pre>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}}
--- expected
<pre>
1
2
3
next
4
5
6
next
7
8
9
0
</pre>

=== for offset:continue big offset
--- input
<pre>
{%for i in array.items limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 %}
{{i}}
{%endfor%}
next
{%for i in array.items offset:continue limit:3 offset:1000 %}
{{i}}
{%endfor%}
</pre>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]}}
--- expected
<pre>
1
2
3
next
4
5
6
next
</pre>

=== for break
--- input
<tt>{%for i in array.items %}{% break %}{%endfor%}</tt>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}}
--- expected
<tt></tt>

=== for after break
--- input
<tt>{%for i in array.items %}{{ i }}{% break %}{%endfor%}</tt>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}}
--- expected
<tt>1</tt>

=== for before break
--- input
<tt>{%for i in array.items %}{% break %}{{ i }}{%endfor%}</tt>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}}
--- expected
<tt></tt>

=== for if break
--- input
<tt>{% for i in array.items %}{{ i }}{% if i > 3 %}{% break %}{% endif %}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}}
--- expected
<tt>1234</tt>

=== for if break nested
--- input
<pre>
{% for item in array %}
{%   for i in item %}
{%     if i == 1 %}{% break %}{% endif %}
{{     i }}
{%   endfor %}
{% endfor %}
</pre>
--- param
+{'array' => [[1,2],[3,4],[5,6]]}
--- expected
<pre>
3
4
5
6
</pre>

=== for unreach break
--- input
<pre>
{% for i in array.items %}
{%   if i == 9999 %}{% break %}{% endif %}
{{   i }}
{% endfor %}
</pre>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<pre>
1
2
3
4
5
</pre>

=== for continue
--- input
<tt>{% for i in array.items %}{% continue %}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<tt></tt>

=== for after continue
--- input
<tt>{% for i in array.items %}{{ i }}{% continue %}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<tt>12345</tt>

=== for before continue
--- input
<tt>{% for i in array.items %}{% continue %}{{ i }}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<tt></tt>

=== for if continue over 3
--- input
<tt>{% for i in array.items %}{% if i > 3 %}{% continue %}{% endif %}{{ i }}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<tt>123</tt>

=== for if continue skip 3
--- input
<tt>{% for i in array.items %}{% if i == 3 %}{% continue %}{% else %}{{ i }}{% endif %}{% endfor %}</tt>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<tt>1245</tt>

=== for if continue nested
--- input
<pre>
{% for item in array %}
{%   for i in item %}
{%     if i == 1 %}{% continue %}{% endif %}
{{     i }}
{%   endfor %}
{% endfor %}
</pre>
--- param
+{'array' => [[1,2],[3,4],[5,6]]}
--- expected
<pre>
2
3
4
5
6
</pre>

=== for unreach continue
--- input
<pre>
{% for i in array.items %}
{%   if i == 9999 %}{% continue %}{% endif %}
{{   i }}
{% endfor %}
</pre>
--- param
+{'array' => {'items' => [1,2,3,4,5]}}
--- expected
<pre>
1
2
3
4
5
</pre>

=== for string
--- input
<tt>{%for val in string%}{{val}}{%endfor%}</tt>
--- param
+{'string' => "test string"}
--- expected
<tt>test string</tt>

=== for string limit: 1
--- input
<tt>{%for val in string limit: 1%}{{val}}{%endfor%}</tt>
--- param
+{'string' => "test string"}
--- expected
<tt>test string</tt>

=== for blank string
--- input
<tt>{% for char in characters %}I WILL NOT BE OUTPUT{% endfor %}</tt>
--- param
+{'characters' => ''}
--- expected
<tt></tt>

=== local scope
--- input
<tt>{%assign x = 'outer' %}{{x}}</tt>
<tt>{%for x in list %} {{x}}{%endfor%}</tt>
<tt>{{x}}</tt>
--- param
+{'list' => ['inner0', 'inner1']}
--- expected
<tt>outer</tt>
<tt> inner0 inner1</tt>
<tt>outer</tt>

