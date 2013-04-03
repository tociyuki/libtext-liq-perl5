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

=== size array 3
--- input
<tt>{{ array | size }}</tt>
--- param
+{'array' => [1, 2, 3]}
--- expected
<tt>3</tt>

=== size array 0
--- input
<tt>{{ array | size }}</tt>
--- param
+{'array' => []}
--- expected
<tt>0</tt>

=== downcase
--- input
<tt>{{ 'Testing' | downcase }}</tt>
--- param
+{}
--- expected
<tt>testing</tt>

=== downcase
--- input
<tt>{{ '' | downcase }}</tt>
--- param
+{}
--- expected
<tt></tt>

=== upcase
--- input
<tt>{{ 'Testing' | upcase }}</tt>
--- param
+{}
--- expected
<tt>TESTING</tt>

=== upcase
--- input
<tt>{{ '' | upcase }}</tt>
--- param
+{}
--- expected
<tt></tt>

=== truncate 10 to 7
--- input
<tt>{{ '1234567890' | truncate:7 }}</tt>
--- param
+{}
--- expected
<tt>1234...</tt>

=== truncate 10 to 20
--- input
<tt>{{ '1234567890' | truncate:20 }}</tt>
--- param
+{}
--- expected
<tt>1234567890</tt>

=== truncate 10 to 0
--- input
<tt>{{ '1234567890' | truncate:0 }}</tt>
--- param
+{}
--- expected
<tt>...</tt>

=== truncate 10 to unspecified
--- input
<tt>{{ '1234567890' | truncate }}</tt>
--- param
+{}
--- expected
<tt>1234567890</tt>

=== split ~
--- input
<tt>{{ '12~34' | split:'~' | join:':' }}</tt>
--- param
+{}
--- expected
<tt>12:34</tt>

=== split ~ ~ ~
--- input
<tt>{{ 'A? ~ ~ ~ ,Z' | split:'~ ~ ~' | join:':' }}</tt>
--- param
+{}
--- expected
<tt>A? : ,Z</tt>

=== split ~
--- input
<tt>{{ 'A?Z' | split:'~' | join:':' }}</tt>
--- param
+{}
--- expected
<tt>A?Z</tt>

=== split x
--- input
<tt>{{ 'AxZ' | split:'x' | join:':' }}</tt>
--- param
+{}
--- expected
<tt>A:Z</tt>

=== escape
--- input
<tt>{{{ '<strong>' | escape }}}</tt>
--- param
+{}
--- expected
<tt>&lt;strong&gt;</tt>

=== h
--- input
<tt>{{{ '<strong>' | h }}}</tt>
--- param
+{}
--- expected
<tt>&lt;strong&gt;</tt>

=== escape_once
--- input
<tt>{{{ '<strong>' | escape | escape_once }}}</tt>
--- param
+{}
--- expected
<tt>&lt;strong&gt;</tt>

=== truncatewords 4
--- input
<tt>{{ 'one two three' | truncatewords:4 }}</tt>
--- param
+{}
--- expected
<tt>one two three</tt>

=== truncatewords 2
--- input
<tt>{{ 'one two three' | truncatewords:2 }}</tt>
--- param
+{}
--- expected
<tt>one two...</tt>

=== truncatewords unspecified
--- input
<tt>{{ 'one two three' | truncatewords }}</tt>
--- param
+{}
--- expected
<tt>one two three</tt>

=== strip_html 1
--- input
<tt>{{ v | strip_html }}</tt>
--- param
+{'v' => q(<div>test</div>)}
--- expected
<tt>test</tt>

=== strip_html 2
--- input
<tt>{{ v | strip_html }}</tt>
--- param
+{'v' => q(<div id='test'>test</div>)}
--- expected
<tt>test</tt>

=== strip_html 3
--- input
<tt>{{ v | strip_html }}</tt>
--- param
+{'v' => 
  q(<script type='text/javascript'>document.write('some stuff');</script>)}
--- expected
<tt></tt>

=== join unspecified
--- input
<tt>{{ v | join }}</tt>
--- param
+{'v' => [1, 2, 3, 4]}
--- expected
<tt>1 2 3 4</tt>

=== join ' - '
--- input
<tt>{{ v | join:' - ' }}</tt>
--- param
+{'v' => [1, 2, 3, 4]}
--- expected
<tt>1 - 2 - 3 - 4</tt>

=== sort 4 3 2 1
--- input
<tt>{{ v | sort | join }}</tt>
--- param
+{'v' => [4, 3, 2, 1]}
--- expected
<tt>1 2 3 4</tt>

=== sort 14 33 2 1
--- input
<tt>{{ v | sort | join }}</tt>
--- param
+{'v' => [14, 33, 2, 1]}
--- expected
<tt>1 14 2 33</tt>

=== nsort 14 33 2 1
--- input
<tt>{{ v | nsort | join }}</tt>
--- param
+{'v' => [14, 33, 2, 1]}
--- expected
<tt>1 2 14 33</tt>

=== map
--- input
<tt>{{ v | map:'a' | join }}</tt>
--- param
+{'v' => [{'a' => 1}, {'a' => 2}, {'a' => 3}, {'a' => 4}]}
--- expected
<tt>1 2 3 4</tt>

=== map
--- input
<tt>{{ v | map:'foo' | map:'bar' | join }}</tt>
--- param
+{
    'v' => [
        {'foo' => {'bar' => 'a'}},
        {'foo' => {'bar' => 'b'}},
        {'foo' => {'bar' => 'c'}},
    ],
}   
--- expected
<tt>a b c</tt>

=== date May
--- input
<tt>{{ '2006-05-05 10:00:00' | date:'%B' }}</tt>
--- param
+{}
--- expected
<tt>May</tt>

=== date June
--- input
<tt>{{ '2006-06-05 10:00:00' | date:'%B' }}</tt>
--- param
+{}
--- expected
<tt>June</tt>

=== date July
--- input
<tt>{{ '2006-07-05 10:00:00' | date:'%B' }}</tt>
--- param
+{}
--- expected
<tt>July</tt>

=== date unspecified fmt
--- input
<tt>{{ '2006-07-05T10:00:00' | date }}</tt>
--- param
+{}
--- expected
<tt>2006-07-05 10:00:00</tt>

=== date empty fmt
--- input
<tt>{{ '2006-07-05T10:00:00' | date:'' }}</tt>
--- param
+{}
--- expected
<tt>2006-07-05 10:00:00</tt>

=== date %m/%d/%Y
--- input
<tt>{{ '2006-07-05 10:00:00' | date:'%m/%d/%Y' }}</tt>
--- param
+{}
--- expected
<tt>07/05/2006</tt>

=== date SQL %b %d %Y
--- input
<tt>{{ '2006-07-05 10:00:00' | date:'%b %d %Y' }}</tt>
--- param
+{}
--- expected
<tt>Jul 05 2006</tt>

=== datetime ISO %b %d %Y
--- input
<tt>{{ '2006-07-05T10:00:00' | date:'%b %d %Y' }}</tt>
--- param
+{}
--- expected
<tt>Jul 05 2006</tt>

=== date %b %d %Y
--- input
<tt>{{ '2006-07-05' | date:'%b %d %Y' }}</tt>
--- param
+{}
--- expected
<tt>Jul 05 2006</tt>

=== date undef
--- input
<tt>{{ null | date }}</tt>
--- param
+{}
--- expected
<tt></tt>

=== date epoch
--- input
<tt>{{ 1152098955 | date:'%m/%d/%Y' }}</tt>
--- param
+{}
--- expected
<tt>07/05/2006</tt>

=== date epoch
--- input
<tt>{{ '1152098955' | date:'%m/%d/%Y' }}</tt>
--- param
+{}
--- expected
<tt>07/05/2006</tt>

=== first
--- input
<tt>{{ v | first }}</tt>
--- param
+{'v' => [1, 2, 3]}
--- expected
<tt>1</tt>

=== last
--- input
<tt>{{ v | last }}</tt>
--- param
+{'v' => [1, 2, 3]}
--- expected
<tt>3</tt>

=== empty first
--- input
<tt>{{ v | first }}</tt>
--- param
+{'v' => []}
--- expected
<tt></tt>

=== empty last
--- input
<tt>{{ v | last }}</tt>
--- param
+{'v' => []}
--- expected
<tt></tt>

=== replace a b
--- input
<tt>{{ 'a a a a' | replace:'a','b' }}</tt>
--- param
+{}
--- expected
<tt>b b b b</tt>

=== replace_first a b
--- input
<tt>{{ 'a a a a' | replace_first:'a','b' }}</tt>
--- param
+{}
--- expected
<tt>b a a a</tt>

=== remove a
--- input
<tt>{{ 'a a a a' | remove:'a' }}</tt>
--- param
+{}
--- expected
<tt>   </tt>

=== remove_first a
--- input
<tt>{{ 'a a a a' | remove_first:'a ' }}</tt>
--- param
+{}
--- expected
<tt>a a a</tt>

=== pipes in string arguments
--- input
<tt>{{ 'foo|bar' | remove:'|' }}</tt>
--- param
+{}
--- expected
<tt>foobar</tt>

=== strip_newlines
--- input
<tt>{{ source | strip_newlines }}</tt>
--- param
+{'source' => "a\nb\nc"}
--- expected
<tt>abc</tt>

=== newline_to_br
--- input
<tt>{{{ source | newline_to_br }}}</tt>
--- param
+{'source' => "a\nb\nc"}
--- expected
<tt>a<br />
b<br />
c</tt>

=== plus 1
--- input
<tt>{{ 1 | plus: 1 }}</tt>
--- param
+{}
--- expected
<tt>2</tt>

=== plus 1.0
--- input
<tt>{{ 1 | plus: 1.0 }}</tt>
--- param
+{}
--- expected
<tt>2</tt>

=== minus 1.0
--- input
<tt>{{ 5 | minus: 1.0 }}</tt>
--- param
+{}
--- expected
<tt>4</tt>

=== minus 2
--- input
<tt>{{ 4.3 | minus: 2 }}</tt>
--- param
+{}
--- expected
<tt>2.3</tt>

=== times 4
--- input
<tt>{{ 3 | times: 4 }}</tt>
--- param
+{}
--- expected
<tt>12</tt>

=== divided_by 12 3
--- input
<tt>{{ 12 | divided_by: 3 }}</tt>
--- param
+{}
--- expected
<tt>4</tt>

=== divided_by 14 3
--- input
<tt>{{ 14 | divided_by: 3 }}</tt>
--- param
+{}
--- expected
<tt>4</tt>

=== modulo 3 2
--- input
<tt>{{ 3 | modulo: 2 }}</tt>
--- param
+{}
--- expected
<tt>1</tt>

=== append 'd'
--- input
<tt>{{ a | append:'d' }}</tt>
--- param
+{'a' => 'bc', 'b' => 'd'}
--- expected
<tt>bcd</tt>

=== append b
--- input
<tt>{{ a | append:b }}</tt>
--- param
+{'a' => 'bc', 'b' => 'd'}
--- expected
<tt>bcd</tt>

=== prepend 'a'
--- input
<tt>{{ a | prepend:'a' }}</tt>
--- param
+{'a' => 'bc', 'b' => 'a'}
--- expected
<tt>abc</tt>

=== append b
--- input
<tt>{{ a | prepend:b }}</tt>
--- param
+{'a' => 'bc', 'b' => 'a'}
--- expected
<tt>abc</tt>

=== attribute class
--- input
<input {{{ foo | attribute:'class'}}}/>
--- param
+{'foo' => 'entry-title'}
--- expected
<input class="entry-title"/>

=== attribute class array
--- input
<input {{{ foo | attribute:'class'}}}/>
--- param
+{'foo' => ['a', 'b', 'c']}
--- expected
<input class="a b c"/>

=== attribute checked
--- input
<input {{{ foo | attribute:'checked'}}}/>
--- param
+{'foo' => 1}
--- expected
<input checked="checked"/>

=== attribute checked false
--- input
<input {{{ foo | attribute:'checked'}}}/>
--- param
+{'foo' => q()}
--- expected
<input />

=== attribute selected
--- input
<input {{{ foo | attribute:'selected'}}}/>
--- param
+{'foo' => 1}
--- expected
<input selected="selected"/>

=== attribute selected false
--- input
<input {{{ foo | attribute:'selected'}}}/>
--- param
+{'foo' => q()}
--- expected
<input />

