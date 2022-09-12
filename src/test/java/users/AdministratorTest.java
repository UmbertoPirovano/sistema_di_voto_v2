package users;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class AdministratorTest {

	@Test
	void testEquals() {
		Administrator a1 = new Administrator("admin","admin");
		Administrator a2 = new Administrator("admin","admin");
		
		assertTrue(a1.equals(a2));
	}
	
	@Test
	void testNotEquals() {
		Administrator a1 = new Administrator("admin","admin");
		Administrator a2 = new Administrator("admin","test");
		
		assertFalse(a1.equals(a2));
	}
}
