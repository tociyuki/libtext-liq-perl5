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

=== basic condition 1 == 2
--- input
<tt>{% if 1 == 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== basic condition 1 == 1
--- input
<tt>{% if 1 == 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 == 1
--- input
<tt>{% if 1 == 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 != 2
--- input
<tt>{% if 1 != 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 <> 2
--- input
<tt>{% if 1 <> 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 < 2
--- input
<tt>{% if 1 < 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 2 > 1
--- input
<tt>{% if 2 > 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 >= 1
--- input
<tt>{% if 1 >= 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 2 >= 1
--- input
<tt>{% if 2 >= 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 <= 2
--- input
<tt>{% if 1 <= 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 <= 1
--- input
<tt>{% if 1 <= 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 > -1
--- input
<tt>{% if 1 > -1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators -1 < 1
--- input
<tt>{% if -1 < 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1.0 > -1.0
--- input
<tt>{% if 1.0 > -1.0 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators -1.0 < 1.0
--- input
<tt>{% if -1.0 < 1.0 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== default operators 1 == 2
--- input
<tt>{% if 1 == 2 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 1 != 1
--- input
<tt>{% if 1 != 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 1 <> 1
--- input
<tt>{% if 1 <> 1 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 1 < 0
--- input
<tt>{% if 1 < 0 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 2 > 4
--- input
<tt>{% if 2 > 4 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 1 >= 3
--- input
<tt>{% if 1 >= 3 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 2 >= 4
--- input
<tt>{% if 2 >= 4 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== default operators 1 <= 0
--- input
<tt>{% if 1 <= 0 %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== contains string o
--- input
<tt>{% if 'bob' contains 'o' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== contains string b
--- input
<tt>{% if 'bob' contains 'b' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== contains string bo
--- input
<tt>{% if 'bob' contains 'bo' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== contains string ob
--- input
<tt>{% if 'bob' contains 'ob' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== contains string bob
--- input
<tt>{% if 'bob' contains 'bob' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>true</tt>

=== contains string bob2
--- input
<tt>{% if 'bob' contains 'bob2' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== contains string a
--- input
<tt>{% if 'bob' contains 'a' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== contains string -
--- input
<tt>{% if 'bob' contains '---' %}true{% else %}false{% endif %}</tt>
--- param
+{}
--- expected
<tt>false</tt>

=== contains array 0
--- input
<tt>{% if array contains 0 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>false</tt>

=== contains array 1
--- input
<tt>{% if array contains 1 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>true</tt>

=== contains array 2
--- input
<tt>{% if array contains 2 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>true</tt>

=== contains array 3
--- input
<tt>{% if array contains 3 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>true</tt>

=== contains array 4
--- input
<tt>{% if array contains 4 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>true</tt>

=== contains array 5
--- input
<tt>{% if array contains 5 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>true</tt>

=== contains array 6
--- input
<tt>{% if array contains 6 %}true{% else %}false{% endif %}</tt>
--- param
+{'array' => [1, 2, 3, 4, 5]}
--- expected
<tt>false</tt>
