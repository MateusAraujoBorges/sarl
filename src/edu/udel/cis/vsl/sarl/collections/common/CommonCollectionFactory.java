/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.collections.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.collections.IF.CollectionFactory;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * Implementation of CollectionFactory using simple array-based data structures
 * 
 * @author siegel
 * 
 */
public class CommonCollectionFactory implements CollectionFactory {

	private ObjectFactory objectFactory;

	private SymbolicSequence<?> emptySequence;

	private CollectionComparator comparator;

	private Comparator<SymbolicExpression> elementComparator;

	public CommonCollectionFactory(ObjectFactory objectFactory) {
		this.objectFactory = objectFactory;
		this.comparator = new CollectionComparator();

		objectFactory.setCollectionComparator(comparator);
	}

	@Override
	public void setElementComparator(Comparator<SymbolicExpression> c) {
		comparator.setElementComparator(c);
		this.elementComparator = c;
	}

	@Override
	public void init() {
		assert elementComparator != null;
		emptySequence = objectFactory
				.canonic(new SimpleSequence<SymbolicExpression>());
	}

	@Override
	public Comparator<SymbolicCollection<? extends SymbolicExpression>> comparator() {
		return comparator;
	}

	@Override
	public <T extends SymbolicExpression> SymbolicSequence<T> sequence(
			Iterable<? extends T> elements) {
		return new SimpleSequence<T>(elements);
	}

	@Override
	public <T extends SymbolicExpression> SymbolicSequence<T> sequence(
			T[] elements) {
		return new SimpleSequence<T>(elements);
	}

	@Override
	public <T extends SymbolicExpression> SymbolicSequence<T> singletonSequence(
			T element) {
		return new SimpleSequence<T>(element);
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T extends SymbolicExpression> SymbolicSequence<T> emptySequence() {
		return (SymbolicSequence<T>) emptySequence;
	}

}
