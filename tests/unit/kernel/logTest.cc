#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "kernel/yosys.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

TEST(KernelLogTest, logvValidValues)
{
	//TODO: Implement log test
	EXPECT_EQ(7, 7);
}

class TestSink : public LogSink {
 public:
	void log(const LogMessage& message) override {
		messages_.push_back(message);
	}
	std::vector<LogMessage> messages_;
};

TEST(KernelLogTest, logToSink)
{
	TestSink sink;
	log_sinks.push_back(&sink);
	log("test info log");
	log_warning("test warning log");

	std::vector<LogMessage> expected{
		LogMessage(LogSeverity::LOG_INFO, "test info log"),
		LogMessage(LogSeverity::LOG_WARNING, "test warning log"),
	};
	// Certain calls to the log.h interface may prepend a string to
	// the provided string. We should ensure that the expected string
	// is a subset of the actual string. Additionally, we don't want to
	// compare timestamps. So, we use a custom comparator.
	for (const LogMessage& expected_msg : expected) {
		EXPECT_THAT(sink.messages_, ::testing::Contains(::testing::Truly(
			[&](const LogMessage& actual) {
				return actual.severity == expected_msg.severity &&
					actual.message.find(expected_msg.message) != std::string::npos;
			}
		)));
	}
	EXPECT_NE(sink.messages_[0].timestamp, 0);
}

YOSYS_NAMESPACE_END
