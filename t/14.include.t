use strict;
use warnings;
use Text::Liq;
use Test::Base;
use Test::Exception;

plan tests => 1 * blocks;

filters {
    'input' => [qw(chomp)],
    'expected' => [qw(chomp)],
    'param' => [qw(eval)],
    'directory' => [qw(eval)],
};

run {
    my($block) = @_;
    my $liq = Text::Liq->parse($block->input);
    my $h = {};
    while (my($k, $v) = each %{$block->directory}) {
        $h->{$k} = Text::Liq->parse($v);
    }
    my $dir = TestDirectory->new($h);

    if ($block->expected eq 'StackFull') {
        throws_ok(sub{
            Text::Liq->render($liq, $block->param, 'directory' => $dir);
        }, qr/StackFull/, $block->name);
    }
    else {
        my $got = Text::Liq->render($liq, $block->param, 'directory' => $dir);
        is $got, $block->expected, $block->name;
    }
};

package TestDirectory;

sub new {
    my($class, $hash) = @_;
    return bless {%{$hash}}, $class;
}

sub get_template_code {
    my($self, $template_path, $context) = @_;
    return $self->{$template_path};
}

__END__

=== include tag with
--- input
<tt>{% include 'product' with products[0] %}</tt>
--- param
+{'products' => [{'title' => 'Draft 151cm'}, {'title' => 'Element 155cm'}]}
--- directory
+{'product' => q(Product: {{ product.title }} )},
--- expected
<tt>Product: Draft 151cm </tt>

=== include tag with default name
--- input
<tt>{% include 'product' %}</tt>
--- param
{'product' => {'title' => 'Draft 151cm'}}
--- directory
+{'product' => q(Product: {{ product.title }} )},
--- expected
<tt>Product: Draft 151cm </tt>

=== include tag for
--- input
<tt>{% include 'product' for products %}</tt>
--- param
{'products' => [{'title' => 'Draft 151cm'}, {'title' => 'Element 155cm'}]}
--- directory
+{'product' => q(Product: {{ product.title }} )},
--- expected
<tt>Product: Draft 151cm Product: Element 155cm </tt>

=== include tag with a literal argument
--- input
<tt>{% include 'locale_variables' echo1: 'test123' %}</tt>
--- param
+{'echo1' => 'foo', 'echo2' => 'bar'}
--- directory
+{'locale_variables' => q(Locale: {{echo1}} {{echo2}})}
--- expected
<tt>Locale: test123 </tt>

=== include tag with literal arguments
--- input
<tt>{% include 'locale_variables' echo1: 'test123' echo2: 'test321' %}</tt>
--- param
+{'echo1' => 'foo', 'echo2' => 'bar'}
--- directory
+{'locale_variables' => q(Locale: {{echo1}} {{echo2}})}
--- expected
<tt>Locale: test123 test321</tt>

=== include tag with literal arguments optional comma
--- input
<tt>{% include 'locale_variables' echo1: 'test123', echo2: 'test321' %}</tt>
--- param
+{'echo1' => 'foo', 'echo2' => 'bar'}
--- directory
+{'locale_variables' => q(Locale: {{echo1}} {{echo2}})}
--- expected
<tt>Locale: test123 test321</tt>

=== include tag with variable arguments
--- input
<tt>{% include 'locale_variables' echo1: echo1 echo2: more_echos.echo2 %}</tt>
--- param
+{'echo1' => 'test123', 'more_echos' => { "echo2" => 'test321'}}
--- directory
+{'locale_variables' => q(Locale: {{echo1}} {{echo2}})}
--- expected
<tt>Locale: test123 test321</tt>

=== include tag with variable arguments optional comma
--- input
<tt>{% include 'locale_variables' echo1: echo1, echo2: more_echos.echo2 %}</tt>
--- param
+{'echo1' => 'test123', 'more_echos' => { "echo2" => 'test321'}}
--- directory
+{'locale_variables' => q(Locale: {{echo1}} {{echo2}})}
--- expected
<tt>Locale: test123 test321</tt>

=== include body nested include body_detail
--- input
<tt>{% include 'body' %}</tt>
--- param
+{}
--- directory
+{
    'body' => q(body {% include 'body_detail' %}),
    'body_detail' => 'body_detail',
}
--- expected
<tt>body body_detail</tt>

=== include nested_template
--- input
<tt>{% include 'nested_template' %}</tt>
--- param
+{}
--- directory
+{
    'nested_template' =>
        q({% include 'header' %} {% include 'body' %} {% include 'footer' %}),
    'header' => 'header',
    'body' => q(body {% include 'body_detail' %}),
    'body_detail' => 'body_detail',
    'footer' => 'footer',
}
--- expected
<tt>header body body_detail footer</tt>

=== include nested_product_template with
--- input
<tt>{% include 'nested_product_template' with product %}</tt>
--- param
+{'product' => {'title' => 'Draft 151cm'}}
--- directory
+{
    'nested_product_template' =>
        q(Product: {{ nested_product_template.title }} {%include 'details' %} ),
    'details' => 'details',
}
--- expected
<tt>Product: Draft 151cm details </tt>

=== include nested_product_template for
--- input
<tt>{% include 'nested_product_template' for products %}</tt>
--- param
+{'products' => [{'title' => 'Draft 151cm'}, {'title' => 'Element 155cm'}]}
--- directory
+{
    'nested_product_template' =>
        q(Product: {{ nested_product_template.title }} {%include 'details' %} ),
    'details' => 'details',
}
--- expected
<tt>Product: Draft 151cm details Product: Element 155cm details </tt>

=== include deeply
--- input
<tt>{% include 'loop' %}</tt>
--- param
+{}
--- directory
+{'loop' => q(!{% include 'loop' %})}
--- expected
StackFull

=== include from variable('Test123')
--- input
<tt>{% include template %}</tt>
--- param
+{'template' => 'Test123'}
--- directory
+{'Test123' => 'Test123', 'Test321' => 'Test321'}
--- expected
<tt>Test123</tt>

=== include from variable('Test321')
--- input
<tt>{% include template %}</tt>
--- param
+{'template' => 'Test321'}
--- directory
+{'Test123' => 'Test123', 'Test321' => 'Test321'}
--- expected
<tt>Test321</tt>

=== include from variable('product')
--- input
<tt>{% include template for product %}</tt>
--- param
+{
    'template' => 'product',
    'product' => { 'title' => 'Draft 151cm'},
}
--- directory
+{'product' => q(Product: {{ product.title }} )}
--- expected
<tt>Product: Draft 151cm </tt>

