package main.symbolTable;

import main.ast.Type.Type;
import main.ast.node.declaration.MethodDeclaration;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.expression.Identifier;

import java.lang.reflect.Method;
import java.util.ArrayList;

public class SymbolTableMethodItem extends SymbolTableItem {

    protected ArrayList<Type> argTypes = new ArrayList<>();
    protected SymbolTable methodSymbolTable;
    protected MethodDeclaration methodDeclaration;
    public static final String METHOD="Method_";

    public SymbolTableMethodItem(String name, ArrayList<Type> argTypes) {
        this.name = name;
        this.argTypes = argTypes;
    }

    public SymbolTableMethodItem( MethodDeclaration methodDeclaration )
    {
        this.name = methodDeclaration.getName().getName();
        this.argTypes = new ArrayList<>();
        for( VarDeclaration arg: methodDeclaration.getArgs() )
            argTypes.add( arg.getType() );
        this.methodDeclaration = methodDeclaration;
    }

    public void setMethodSymbolTable( SymbolTable symTable )
    {
        this.methodSymbolTable = symTable;
    }

    public SymbolTable getMethodSymbolTable()
    {
        return this.methodSymbolTable;
    }

    public void setMethodDeclaration( MethodDeclaration methodDeclaration )
    {
        this.methodDeclaration = methodDeclaration;
    }
    public String getName()
    {
        return name;
    }
    public void setName( String name )
    {
        this.name = name;
        methodDeclaration.getName().setName( name );
    }
    public MethodDeclaration getMethodDeclaration()
    {
        return methodDeclaration;
    }
    @Override
    public String getKey() {
        //todo
        return SymbolTableMethodItem.METHOD + this.name;
    }
}
