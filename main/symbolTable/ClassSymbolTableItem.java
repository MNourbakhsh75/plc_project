package main.symbolTable;

import main.ast.node.declaration.ClassDeclaration;
import main.ast.node.expression.Identifier;

public class ClassSymbolTableItem extends SymbolTableItem {
    public static final String CLASS="Class_";
    protected SymbolTable classSym;
    protected ClassDeclaration classDeclaration;
    public ClassSymbolTableItem( ClassDeclaration classDeclaration )
    {
        this.name = classDeclaration.getName().getName();
        this.classDeclaration = classDeclaration;
    }
    @Override
    public String getKey()
    {
        return ClassSymbolTableItem.CLASS + name;
    }
    public void setSymbolTable( SymbolTable classSym )
    {
        this.classSym = classSym;
    }
    public SymbolTable getClassSym()
    {
        return classSym;
    }

    public void setName( String name )
    {
        this.name = name;
        this.classDeclaration.getName().setName( name );
    }
    public String getParentName()
    {
        if( classDeclaration.getParentName() == null )
            return null;
        return classDeclaration.getParentName().getName();
    }
    public void setParentName( String parentName )
    {
        classDeclaration.getParentName().setName( parentName );
    }

    public void setClassDeclaration( ClassDeclaration classDeclaration )
    {
        this.classDeclaration = classDeclaration;
    }
    public ClassDeclaration getClassDeclaration()
    {
        return classDeclaration;
    }

}
