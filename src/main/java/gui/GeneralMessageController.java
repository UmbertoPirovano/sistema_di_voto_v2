package gui;

import java.net.URL;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.text.Font;
import javafx.scene.text.FontPosture;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;

public class GeneralMessageController implements Initializable {
	
	private final String message;
	
    @FXML
    private TextFlow textFlow;
    
    @FXML
    private Button dismissButton;

    @FXML
    void handleDismissButton(ActionEvent event) {
    	dismissButton.getScene().getWindow().hide();
    }
    
    public GeneralMessageController(String s) {
    	message = Objects.requireNonNull(s);
    }
    
	@Override
	public void initialize(URL location, ResourceBundle resources) {
		Text msg = new Text(message);
		msg.setFont(Font.font("Helvetica", FontPosture.ITALIC, 18));
		textFlow.getChildren().add(msg);		
	}

}
