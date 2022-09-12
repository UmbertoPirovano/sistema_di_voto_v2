package gui;

import javafx.beans.property.SimpleStringProperty;

public class RowLog {
	private final SimpleStringProperty log;
	
	public RowLog(String log) {
		this.log = new SimpleStringProperty(log);
	}
	
	public String getLog() {
		return log.get();
	}
}
