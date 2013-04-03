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

=== true eq true
--- input
<tt> {% if true == true %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== true ne true
--- input
<tt> {% if true != true %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  false  </tt>

=== zero gt zero
--- input
<tt> {% if 0 > 0 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  false  </tt>

=== one gt zero
--- input
<tt> {% if 1 > 0 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== zero lt one
--- input
<tt> {% if 0 < 1 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== zero le zero
--- input
<tt> {% if 0 <= 0 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== null le zero
--- input
<tt> {% if null <= 0 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  false  </tt>

=== zero le null
--- input
<tt> {% if 0 <= null %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  false  </tt>

=== zero ge zero
--- input
<tt> {% if 0 >= 0 %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== str eq str
--- input
<tt> {% if 'test' == 'test' %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  true  </tt>

=== str ne str
--- input
<tt> {% if 'test' != 'test' %} true {% else %} false {% endif %} </tt>
--- param
+{}
--- expected
<tt>  false  </tt>

=== var eq double-quoted
--- input
<tt> {% if var == "hello there!" %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 'hello there!'}
--- expected
<tt>  true  </tt>

=== double-quoted eq var
--- input
<tt> {% if "hello there!" == var %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 'hello there!'}
--- expected
<tt>  true  </tt>

=== var eq single-quoted
--- input
<tt> {% if var == 'hello there!' %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 'hello there!'}
--- expected
<tt>  true  </tt>

=== single-quoted eq var
--- input
<tt> {% if 'hello there!' == var %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 'hello there!'}
--- expected
<tt>  true  </tt>

=== array eq empty
--- input
<tt> {% if array == empty %} true {% else %} false {% endif %} </tt>
--- param
+{'array' => []}
--- expected
<tt>  true  </tt>

=== array 3 eq empty
--- input
<tt> {% if array == empty %} true {% else %} false {% endif %} </tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt>  false  </tt>

=== var undef eq nil
--- input
<tt> {% if var == nil %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => undef}
--- expected
<tt>  true  </tt>

=== var undef eq null
--- input
<tt> {% if var == null %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => undef}
--- expected
<tt>  true  </tt>

=== var 1 eq nil
--- input
<tt> {% if var != nil %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 1}
--- expected
<tt>  true  </tt>

=== var 1 eq null
--- input
<tt> {% if var != null %} true {% else %} false {% endif %} </tt>
--- param
+{'var' => 1}
--- expected
<tt>  true  </tt>

