package main.symbolTable.symbolTableVariable;

import main.ast.Type.Type;
import main.ast.node.declaration.VarDeclaration;
import main.symbolTable.SymbolTableItem;

public abstract class SymbolTableVariableItemBase extends SymbolTableItem {

    public static final String VARIABLE = "Variable_";
	protected int index;
	protected Type type;
	protected VarDeclaration varDeclaration;

	
	public SymbolTableVariableItemBase(String name, Type type, int index) {
		this.name = name;
	    this.type = type;
	    this.index = index;
	}
	public SymbolTableVariableItemBase( VarDeclaration varDeclaration )
    {
        this.name = varDeclaration.getIdentifier().getName();
        this.type = varDeclaration.getType();
        this.index = 0;
        this.varDeclaration = varDeclaration;
    }

	public String getName() {
		return name;
	}
	public void setName( String name )
    {
        this.name = name;
        varDeclaration.getIdentifier().setName( name );
    }

	public Type getType() {
		return type;
	}

	@Override
	public String getKey() {
		return SymbolTableVariableItemBase.VARIABLE + name;
	}

    public int getIndex() {
        return index;
    }
    public void setIndex( int index )
    {
        this.index = index;
    }
    public VarDeclaration getVarDeclaration()
    {
        return varDeclaration;
    }
    public void setVarDeclaration( VarDeclaration varDeclaration )
    {
        this.varDeclaration = varDeclaration;
    }
}