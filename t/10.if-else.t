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

=== if false end
--- input
<tt>{% if false %} this text should not go into the output {% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if true end
--- input
<tt>{% if true %} this text should go into the output {% endif %}</tt>
--- param
+{}
--- expected
<tt> this text should go into the output </tt>

=== if true end
--- input
<tt>{% if false %} you suck {% endif %} {% if true %} you rock {% endif %}?</tt>
--- param
+{}
--- expected
<tt>  you rock ?</tt>

=== if false else end
--- input
<tt>{% if false %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if true else end
--- input
<tt>{% if true %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if "foo" else end
--- input
<tt>{% if "foo" %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if var_true else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => 1==1}
--- expected
<tt> THEN </tt>

=== if var_false else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => 1!=1}
--- expected
<tt> ELSE </tt>

=== if true or true end
--- input
<tt>{% if a or b %} THEN {% endif %}</tt>
--- param
+{'a' => 1==1, 'b' => 1==1}
--- expected
<tt> THEN </tt>

=== if true or false end
--- input
<tt>{% if a or b %} THEN {% endif %}</tt>
--- param
+{'a' => 1==1, 'b' => 1!=1}
--- expected
<tt> THEN </tt>

=== if false or true end
--- input
<tt>{% if a or b %} THEN {% endif %}</tt>
--- param
+{'a' => 1!=1, 'b' => 1==1}
--- expected
<tt> THEN </tt>

=== if false or false end
--- input
<tt>{% if a or b %} THEN {% endif %}</tt>
--- param
+{'a' => 1!=1, 'b' => 1!=1}
--- expected
<tt></tt>

=== if false or false or true end
--- input
<tt>{% if a or b or c %} THEN {% endif %}</tt>
--- param
+{'a' => 1!=1, 'b' => 1!=1, 'c' => 1==1}
--- expected
<tt> THEN </tt>

=== if false or false or false end
--- input
<tt>{% if a or b or c %} THEN {% endif %}</tt>
--- param
+{'a' => 1!=1, 'b' => 1!=1, 'c' => 1!=1}
--- expected
<tt></tt>

=== if a == true or b == true end
--- input
<tt>{% if a == true or b == true %} THEN {% endif %}</tt>
--- param
+{'a' => 1==1, 'b' => 1==1}
--- expected
<tt> THEN </tt>

=== if a == true or b == false end
--- input
<tt>{% if a == true or b == false %} THEN {% endif %}</tt>
--- param
+{'a' => 1==1, 'b' => 1==1}
--- expected
<tt> THEN </tt>

=== if a == false or b == false end
--- input
<tt>{% if a == false or b == false %} THEN {% endif %}</tt>
--- param
+{'a' => 1==1, 'b' => 1==1}
--- expected
<tt></tt>

=== if a == false or b == false end
--- input
<tt>{% if a == 'and'
      and b == 'or'
      and c == 'foo and bar'
      and d == 'bar or baz'
      and e == 'foo'
      and foo
      and bar %} THEN {% endif %}</tt>
--- param
+{
    'a' => 'and',
    'b' => 'or',
    'c' => 'foo and bar',
    'd' => 'bar or baz',
    'e' => 'foo',
    'foo' => 1==1,
    'bar' => 1==1,
}
--- expected
<tt> THEN </tt>

=== if android.name end
--- input
<tt>{% if android.name == 'Roy' %}YES{% endif %}</tt>
--- param
+{'order' => {'items_count' => 0}, 'android' => {'name' => 'Roy'}}
--- expected
<tt>YES</tt>

=== if order.items_count end
--- input
<tt>{% if order.items_count == 0 %}YES{% endif %}</tt>
--- param
+{'order' => {'items_count' => 0}, 'android' => {'name' => 'Roy'}}
--- expected
<tt>YES</tt>

=== if true and true end
--- input
<tt>{% if true and true %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if true and false end
--- input
<tt>{% if true and false %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if false and true end
--- input
<tt>{% if false and true %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if false and false end
--- input
<tt>{% if false and false %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if foo.bar(not exists)
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {}}
--- expected
<tt></tt>

=== if var(false) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => 1!=1}
--- expected
<tt></tt>

=== if var(undef) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => undef}
--- expected
<tt></tt>

=== if foo.bar(false) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => 1!=1}}
--- expected
<tt></tt>

=== if foo.bar(not exists) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {}}
--- expected
<tt></tt>

=== if foo(undef).bar end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => undef}
--- expected
<tt></tt>

=== if foo(true).bar end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => 1==1}
--- expected
<tt></tt>

=== if var("text") end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => "text"}
--- expected
<tt> THEN </tt>

=== if var(true) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => 1==1}
--- expected
<tt> THEN </tt>

=== if var(1) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => 1}
--- expected
<tt> THEN </tt>

=== if var([]) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => []}
--- expected
<tt> THEN </tt>

=== if var({}) end
--- input
<tt>{% if var %} THEN {% endif %}</tt>
--- param
+{'var' => {}}
--- expected
<tt> THEN </tt>

=== if "foo" end
--- input
<tt>{% if "foo" %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if foo.bar(true) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => 1==1}}
--- expected
<tt> THEN </tt>

=== if foo.bar("text") end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => "text"}}
--- expected
<tt> THEN </tt>

=== if foo.bar(1) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => 1}}
--- expected
<tt> THEN </tt>

=== if foo.bar({}) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => {}}}
--- expected
<tt> THEN </tt>

=== if foo.bar([]) end
--- input
<tt>{% if foo.bar %} THEN {% endif %}</tt>
--- param
+{'foo' => {'bar' => []}}
--- expected
<tt> THEN </tt>

=== if var(false) else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => 1!=1}
--- expected
<tt> ELSE </tt>

=== if var(undef) else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => undef}
--- expected
<tt> ELSE </tt>

=== if var(true) else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => 1==1}
--- expected
<tt> THEN </tt>

=== if var("text") else end
--- input
<tt>{% if var %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'var' => "text"}
--- expected
<tt> THEN </tt>

=== if foo.bar(false) else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'foo' => {'bar' => 1!=1}}
--- expected
<tt> ELSE </tt>

=== if foo.bar(true) else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'foo' => {'bar' => 1==1}}
--- expected
<tt> THEN </tt>

=== if foo.bar("text") else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'foo' => {'bar' => "text"}}
--- expected
<tt> THEN </tt>

=== if foo.bar(not exists) else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'foo' => {'notbar' => 1==1}}
--- expected
<tt> ELSE </tt>

=== if foo.bar(not exists) else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'foo' => {}}
--- expected
<tt> ELSE </tt>

=== if foo(not exists).bar else end
--- input
<tt>{% if foo.bar %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{'notfoo' => {'bar' => 1==1}}
--- expected
<tt> ELSE </tt>

=== if false if false end end
--- input
<tt>{% if false %}{% if false %} THEN {% endif %}{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if false if true end end
--- input
<tt>{% if false %}{% if true %} THEN {% endif %}{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if true if false end end
--- input
<tt>{% if true %}{% if false %} THEN {% endif %}{% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

=== if true if false end end
--- input
<tt>{% if true %}{% if true %} A {% endif %}{% endif %}</tt>
--- param
+{}
--- expected
<tt> A </tt>

=== if true if true else end else end
--- input
<tt>{% if true %}{% if true %}A{% else %}B{% endif %}{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>A</tt>

=== if true if false else end else end
--- input
<tt>{% if true %}{% if false %}A{% else %}B{% endif %}{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>B</tt>

=== if true if false else end else end
--- input
<tt>{% if false %}{% if true %}A{% else %}B{% endif %}{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>C</tt>

=== if null < 10 end
--- input
<tt>{% if null < 10 %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if null <= 10 end
--- input
<tt>{% if null <= 10 %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if null >= 10 end
--- input
<tt>{% if null >= 10 %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if null > 10 end
--- input
<tt>{% if null > 10 %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if 10 < null end
--- input
<tt>{% if 10 < null %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if 10 <= null end
--- input
<tt>{% if 10 <= null %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if 10 >= null end
--- input
<tt>{% if 10 >= null %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if 10 > null end
--- input
<tt>{% if 10 > null %} THEN {% else %} ELSE {% endif %}</tt>
--- param
+{}
--- expected
<tt> ELSE </tt>

=== if 0 == 0 elsif 1 == 1 else end
--- input
<tt>{% if 0 == 0 %}A{% elsif 1 == 1%}B{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>A</tt>

=== if 0 != 0 elsif 1 == 1 else end
--- input
<tt>{% if 0 != 0 %}A{% elsif 1 == 1%}B{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>B</tt>

=== if 0 != 0 elsif 1 != 1 else end
--- input
<tt>{% if 0 != 0 %}A{% elsif 1 != 1%}B{% else %}C{% endif %}</tt>
--- param
+{}
--- expected
<tt>C</tt>

=== if false elsif true end
--- input
<tt>{% if false %}A{% elsif true %}B{% endif %}</tt>
--- param
+{}
--- expected
<tt>B</tt>

=== if contains end
--- input
<tt>{% if 'bob' contains 'o' %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if contains end
--- input
<tt>{% if 'bob' contains 'bob' %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt> THEN </tt>

=== if contains end
--- input
<tt>{% if 'bob' contains 'a' %} THEN {% endif %}</tt>
--- param
+{}
--- expected
<tt></tt>

