package main.symbolTable;

import main.symbolTable.itemException.ItemAlreadyExistsException;
import main.symbolTable.itemException.ItemNotFoundException;

import java.util.*;

public class SymbolTable {

	SymbolTable pre;
	HashMap<String, SymbolTableItem> items;

	// Static members region

	public static SymbolTable top;
	public static SymbolTable root;
	
	private static Stack<SymbolTable> stack = new Stack<SymbolTable>();

	// Use it in pass 1 scope start
	public static void push(SymbolTable symbolTable) {
		if(top != null)
			stack.push(top);
		top = symbolTable;
	}

	public int getItemCount()
    {
        return items.size();
    }


	// Use it in pass1 scope end
	public static void pop() {
		top = stack.pop();
	}

	// End of static members region

    protected int lastUsedIndex;
	public SymbolTable() {
	    this(null);
	}

	public SymbolTable(SymbolTable pre) {
		this.pre = pre;
		this.items = new HashMap<String, SymbolTableItem>();
		this.lastUsedIndex = 1;
	}


	public void put(SymbolTableItem item) throws ItemAlreadyExistsException {
		if(items.containsKey(item.getKey()))
			throw new ItemAlreadyExistsException();
		items.put(item.getKey(), item);
	}

	public int getLastUsedIndex()
    {
        return lastUsedIndex;
    }

	public SymbolTableItem getInCurrentScope(String key) throws ItemNotFoundException {
		SymbolTableItem value = items.get(key);
        if( value == null )
		    throw new ItemNotFoundException();
		return value;
	}

	public SymbolTableItem get(String key) throws ItemNotFoundException {
		SymbolTableItem value = items.get(key);
		if(value == null && pre != null)
			return pre.get(key);
		else if(value == null)
			throw new ItemNotFoundException();
		else
			return value;
	}

	public void updateItemInCurrentScope( String prevKey , SymbolTableItem newItem )
			throws ItemNotFoundException
	{
		SymbolTableItem value = items.get( prevKey );
		if(value == null)
			throw new ItemNotFoundException();
		else {
		    items.remove( prevKey );
            items.put(newItem.getKey(), newItem);
        }
	}
	public HashMap< String , SymbolTableItem> getSymItems()
    {
        return items;
    }

	public SymbolTable getPreSymbolTable() {
		return pre;
	}
	public void setPreSymbolTable( SymbolTable pre )
	{
		this.pre = pre;
	}
}