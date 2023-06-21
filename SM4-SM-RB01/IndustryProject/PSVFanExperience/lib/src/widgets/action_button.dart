import 'package:flutter/material.dart';
import 'package:provider/provider.dart';

import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/models/submission.dart';

class ActionButton extends StatefulWidget {
  const ActionButton({
    required this.submission,
    required this.showStat,
    required this.icon,
    required this.callback,
    this.accentIcon,
    super.key
  });

  final Submission submission;
  final bool showStat;
  final Icon icon;
  final Icon? accentIcon;
  final void Function() callback;

  @override
  ActionButtonState createState() => ActionButtonState();
}

class ActionButtonState extends State<ActionButton> {
  @override
  Widget build(BuildContext context) {
    return Consumer<SubmissionProvider>(
      builder: (builder, provider, _) => GestureDetector(
        onTap: () => widget.callback(),
        child: SizedBox(
          width: MediaQuery.of(context).size.width * .2,
          height: MediaQuery.of(context).size.height * .07,
          child: Stack(
            alignment: AlignmentDirectional.topCenter,
            children: [
              Image.asset("assets/images/rectangle-70.png"),
              Positioned.fill(
                child: Align(
                  alignment: Alignment.topRight,
                  child: Padding(
                    padding: EdgeInsets.only(
                      right: MediaQuery.of(context).size.width * .035,
                    ),
                    child: SizedBox(
                      child: provider.getSubmission(widget.submission).isLikedByUser ? widget.accentIcon != null ? widget.accentIcon! : widget.icon : widget.icon,
                      width: MediaQuery.of(context).size.width * .075,
                      height: MediaQuery.of(context).size.height * .05,
                    ),
                  )
                ),
              ),
              widget.showStat ? Positioned.fill(
                child: Align(
                  alignment: Alignment.bottomLeft,
                  child: Padding(
                    padding: EdgeInsets.only(
                      left: MediaQuery.of(context).size.width * .04,
                      bottom: MediaQuery.of(context).size.height * .005,
                    ),
                    child: Text(
                      provider.getSubmission(widget.submission).likes.toString(),
                      style: TextStyle(
                        color: Theme.of(context).colorScheme.tertiary,
                        fontSize: 24
                      ),
                    ),
                  )
                ),
              ) : Container(),
            ]
          ),
        ),
      ),
    );
  }
}