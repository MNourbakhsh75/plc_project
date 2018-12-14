package main.ast.node.declaration;

import main.visitor.Visitor;
import main.ast.node.expression.Identifier;

public class MainMethodDeclaration extends MethodDeclaration{
    public MainMethodDeclaration(Identifier name) {
        super( name );
    }


    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
