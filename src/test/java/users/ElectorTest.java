package users;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class ElectorTest {
	
	/**
	 * Testa il funzionameto del metodo equals di Elector nel caso di confronto tra due Elector uguali.
	 */
	@Test
	public void testNotEquals() {
		Elector e1 = new Elector("mattia","mattia","Mattia","Garavaglia");
		Elector e2 = new Elector("umberto","umberto","Umberto","Pirovano");
		assertNotEquals(e1,e2);
	}
	
	/**
	 * Testa il funzionameto del metodo equals di Elector nel caso di confronto tra due Elector diversi.
	 */
	@Test
	public void testEquals() {
		Elector e1 = new Elector("mattia","mattia","Mattia","Garavaglia");
		Elector e2 = new Elector("mattia","test","Mattia","Garavaglia");
		
		assertEquals(e1,e2);
	}

}
